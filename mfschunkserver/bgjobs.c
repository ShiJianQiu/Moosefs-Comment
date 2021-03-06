/*
 * Copyright (C) 2020 Jakub Kruszona-Zawadzki, Core Technology Sp. z o.o.
 * 
 * This file is part of MooseFS.
 * 
 * MooseFS is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, version 2 (only).
 * 
 * MooseFS is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with MooseFS; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02111-1301, USA
 * or visit http://www.gnu.org/licenses/gpl-2.0.html
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <syslog.h>
#include <inttypes.h>
//#include <fcntl.h>
//#include <sys/ioctl.h>
#include <limits.h>
#include <signal.h>
#include <pthread.h>
#include <errno.h>

#include "main.h"
#include "cfg.h"
#include "pcqueue.h"
#include "lwthread.h"
#include "datapack.h"
#include "massert.h"

#include "mainserv.h"
#include "hddspacemgr.h"
#include "replicator.h"
#include "masterconn.h"

#define JHASHSIZE 0x400
#define JHASHPOS(id) ((id)&0x3FF)

enum {
	JSTATE_DISABLED,	//禁用状态，当cs与master或client断开连接时会将所有的还未处理的job设置为该状态
	JSTATE_ENABLED,		//使能状态，新建job时会设置该状态，表示job还未处理
	JSTATE_INPROGRESS	//运行状态，在线程函数处理该job记录的块操作时会设置为该状态
};

enum {
	OP_EXIT=0,
	OP_INVAL,
//	OP_MAINSERV,
	OP_CHUNKOP,
//	OP_OPEN,
//	OP_CLOSE,
//	OP_READ,
//	OP_WRITE,
	OP_SERV_READ,
	OP_SERV_WRITE,
	OP_REPLICATE,
	OP_GETBLOCKS,
	OP_GETCHECKSUM,
	OP_GETCHECKSUMTAB,
	OP_CHUNKMOVE,
};//块操作类型，实际会记录到队列元素中,即queue. op，在线程处理块操作时，会从队列中取出job的同时取出该值以确定块操作的类型

// for OP_CHUNKOP
/*一般块文件操作参数，主要来自master的消息请求，
包括块创建、删除、更新version、截断、拷贝、截断+拷贝（即3.4节中介绍的大部分消息请求）*/
typedef struct _chunk_op_args {
	uint64_t chunkid,copychunkid;
	uint32_t version,newversion,copyversion;
	uint32_t length;
} chunk_op_args;
/*
// for OP_OPEN and OP_CLOSE
typedef struct _chunk_oc_args {
	uint64_t chunkid;
	uint32_t version;
} chunk_oc_args;

// for OP_READ
typedef struct _chunk_rd_args {
	uint64_t chunkid;
	uint32_t version;
	uint32_t offset,size;
	uint16_t blocknum;
	uint8_t *buffer;
	uint8_t *crcbuff;
} chunk_rd_args;

// for OP_WRITE
typedef struct _chunk_wr_args {
	uint64_t chunkid;
	uint32_t version;
	uint32_t offset,size;
	uint16_t blocknum;
	const uint8_t *buffer;
	const uint8_t *crcbuff;
} chunk_wr_args;
*/

// for OP_SERV_READ and OP_SERV_WRITE
typedef struct _chunk_rw_args {
	int sock;
	const uint8_t *packet;
	uint32_t length;
} chunk_rw_args;//块读写操作

// for OP_REPLICATE
typedef struct _chunk_rp_args {
	uint64_t chunkid;
	uint32_t version;
	uint32_t xormasks[4];
	uint8_t srccnt;
} chunk_rp_args;//块文件的跨cs拷贝操作参数，一般在做负载均衡时会发送该消息请求REPLICATE

// for OP_GETBLOCKS, OP_GETCHECKSUM and OP_GETCHECKSUMTAB
typedef struct _chunk_ij_args {
	uint64_t chunkid;
	uint32_t version;
	void *pointer;
} chunk_ij_args;

// for OP_CHUNKMOVE
typedef struct _chunk_mv_args {
	void *fsrc;
	void *fdst;
} chunk_mv_args;

typedef struct _job {
	uint32_t jobid;//id，由jobpoo. nextjobid++获得，（0值除外）
	void (*callback)(uint8_t status,void *extra);//回调函数，一般是用于组织和发送返回信息
	void *extra;//回调函数的参数，一般是返回信息的一部分（缺少status）
	void *args;//块操作需要的参数，包括chunkid、version、buffer、offset等，按照操作类型分别定义为chunk_rw_args、chunk_rp_args、chunk_ij_args 、chunk_mv_args
	uint8_t jstate;//job的状态，包括JSTATE_DISABLED、JSTATE_ENABLED和JSTATE_INPROGRESS
	// JSTATE_DISABLED,	//禁用状态
	// JSTATE_ENABLED,		//使能状态
	// JSTATE_INPROGRESS	//运行状态
	struct _job *next;//指向下一个job结构
} job;//job,保存了一个块操作所需要的参数和返回信息处理

typedef struct _jobpool {
	int rpipe,wpipe;//一个管道的读写描述符，用于激活消息请求的响应（返回status）
	int32_t fdpdescpos;
	uint32_t workers_max;//线程最大值
	uint32_t workers_himark;//用于区别hlstatus
	uint32_t workers_lomark;//用于区别hlstatus
	uint32_t workers_max_idle;
	uint32_t workers_avail;//线程空余？
	uint32_t workers_total;//线程总数
	uint32_t workers_term_waiting;
	pthread_cond_t worker_term_cond;
	pthread_mutex_t pipelock;//rpipe,wpipe的互斥锁
	pthread_mutex_t jobslock;//job的互斥锁，更具体是job. jstate的互斥锁
	void *jobqueue;//指向job的队列（queue）指针
	void *statusqueue;//指向status的队列（queue）指针
	job* jobhash[JHASHSIZE];//job的hash链表数组，所有job的存储结构
	uint32_t nextjobid;//保存下一个job的id
} jobpool;//工作池，在与master和client消息交互中都会使用到，在mfschunkserver/masterconn和mfschunkserver/csserv.c中都单独定义了自己的jpool指针变量

typedef struct _worker {
	pthread_t thread_id;//线程描述符所在的数组，每个元素为一个线程的ID	
	jobpool *jp;
} worker;

static jobpool* globalpool = NULL;

static uint32_t stats_maxjobscnt = 0;
static uint32_t last_maxjobscnt = 0;

// static uint8_t exiting;

void job_stats(uint32_t *maxjobscnt) {
	*maxjobscnt = last_maxjobscnt = stats_maxjobscnt;
	stats_maxjobscnt = 0;
}

uint32_t job_getload(void) {
	return last_maxjobscnt;
}

static inline void job_send_status(jobpool *jp,uint32_t jobid,uint8_t status) {
	zassert(pthread_mutex_lock(&(jp->pipelock)));
	if (queue_isempty(jp->statusqueue)) {	// first status
		eassert(write(jp->wpipe,&status,1)==1);	// write anything to wake up select
	}
	queue_put(jp->statusqueue,jobid,status,NULL,1);
	zassert(pthread_mutex_unlock(&(jp->pipelock)));
	return;
}

static inline int job_receive_status(jobpool *jp,uint32_t *jobid,uint8_t *status) {
	uint32_t qstatus;
	zassert(pthread_mutex_lock(&(jp->pipelock)));
	queue_get(jp->statusqueue,jobid,&qstatus,NULL,NULL);
	*status = qstatus;
	if (queue_isempty(jp->statusqueue)) {
		eassert(read(jp->rpipe,&qstatus,1)==1);	// make pipe empty
		zassert(pthread_mutex_unlock(&(jp->pipelock)));
		return 0;	// last element
	}
	zassert(pthread_mutex_unlock(&(jp->pipelock)));
	return 1;	// not last
}

void* job_worker(void *arg);

static uint32_t lastnotify = 0;

static inline void job_spawn_worker(jobpool *jp) {
	worker *w;

	w = malloc(sizeof(worker));
	passert(w);
	w->jp = jp;
	if (lwt_minthread_create(&(w->thread_id),0,job_worker,w)<0) {
		return;
	}
	jp->workers_avail++;
	jp->workers_total++;
	if (jp->workers_total%10==0 && lastnotify!=jp->workers_total) {
		syslog(LOG_NOTICE,"workers: %"PRIu32"+",jp->workers_total);
		lastnotify = jp->workers_total;
	}
//	syslog(LOG_NOTICE,"jobs: spawn worker (total: %"PRIu32")",jp->workers_total);
}

static inline void job_close_worker(worker *w) {
	jobpool *jp = w->jp;
	jp->workers_avail--;
	jp->workers_total--;
	if (jp->workers_total==0 && jp->workers_term_waiting) {
		zassert(pthread_cond_signal(&(jp->worker_term_cond)));
		jp->workers_term_waiting--;
	}
	pthread_detach(w->thread_id);
	free(w);
	if (jp->workers_total%10==0 && lastnotify!=jp->workers_total) {
		syslog(LOG_NOTICE,"workers: %"PRIu32"-",jp->workers_total);
		lastnotify = jp->workers_total;
	}
//	syslog(LOG_NOTICE,"jobs: close worker (total: %"PRIu32")",jp->workers_total);
}

#define opargs ((chunk_op_args*)(jptr->args))
// #define ocargs ((chunk_oc_args*)(jptr->args))
// #define rdargs ((chunk_rd_args*)(jptr->args))
// #define wrargs ((chunk_wr_args*)(jptr->args))
#define rwargs ((chunk_rw_args*)(jptr->args))
#define rpargs ((chunk_rp_args*)(jptr->args))
#define ijargs ((chunk_ij_args*)(jptr->args))
#define mvargs ((chunk_mv_args*)(jptr->args))
/**
 * job_worker函数是各类块操作的线程实体，它内部实际是一个死循环，
 * 主要工作流程是：
 * 调用queue_get从jobqueue队列中取出一个job以及块操作类型op
 * （在queue_get中可能因为取不到队列元素而阻塞，在将来某一时刻又因为有新的队列元素而被唤醒）;
 * 若job. jstate为JSTATE_ENABLED则设置为JSTATE_INPROGRESS；
 * swich-case语句根据块操作类型op调用响应的块操作处理函数
 * （ps：op=OP_INVAL时直接设置status = ERROR_EINVAL表示消息请求中传递参数出错；op=OP_EXIT时线程返回退出）；
 * 调用job_send_status函数将status放置到statusqueue队列中并写管道wpipe以通知mfschunkserver主线程处理返回信息。
 * */
void* job_worker(void *arg) {
	worker *w = (worker*)arg;
	jobpool *jp = w->jp;
	job *jptr;
	uint8_t *jptrarg;
	uint8_t status,jstate;
	uint32_t jobid;
	uint32_t op;

//	syslog(LOG_NOTICE,"worker %p started (jobqueue: %p ; jptr:%p ; jptrarg:%p ; status:%p )",(void*)pthread_self(),jp->jobqueue,(void*)&jptr,(void*)&jptrarg,(void*)&status);
	for (;;) {
		queue_get(jp->jobqueue,&jobid,&op,&jptrarg,NULL);
//		syslog(LOG_NOTICE,"job worker got job: %"PRIu32",%"PRIu32,jobid,op);
		jptr = (job*)jptrarg;
		zassert(pthread_mutex_lock(&(jp->jobslock)));
		if (jobid==0 && op==0 && jptrarg==NULL) { // queue has been closed
			job_close_worker(w);
			zassert(pthread_mutex_unlock(&(jp->jobslock)));
			return NULL;
		}
		jp->workers_avail--;
		if (jp->workers_avail==0 && jp->workers_total<jp->workers_max) {
			job_spawn_worker(jp);
		}
		if (jptr!=NULL) {
			jstate=jptr->jstate;
			if (jptr->jstate==JSTATE_ENABLED) {
				jptr->jstate=JSTATE_INPROGRESS;
			}
		} else {
			jstate=JSTATE_DISABLED;
		}
		zassert(pthread_mutex_unlock(&(jp->jobslock)));
		switch (op) {
			case OP_INVAL:
				status = MFS_ERROR_EINVAL;
				break;
/*
			case OP_MAINSERV:
				if (jstate==JSTATE_DISABLED) {
					status = MFS_ERROR_NOTDONE;
				} else {
					mainserv_serve(*((int*)(jptr->args)));
					status = MFS_STATUS_OK;
				}
				break;
*/
			case OP_CHUNKOP:
				if (jstate==JSTATE_DISABLED) {
					status = MFS_ERROR_NOTDONE;
				} else {
					status = hdd_chunkop(opargs->chunkid,opargs->version,opargs->newversion,opargs->copychunkid,opargs->copyversion,opargs->length);
				}
				break;
/*
			case OP_OPEN:
				if (jstate==JSTATE_DISABLED) {
					status = MFS_ERROR_NOTDONE;
				} else {
					status = hdd_open(ocargs->chunkid,ocargs->version);
				}
				break;
			case OP_CLOSE:
				if (jstate==JSTATE_DISABLED) {
					status = MFS_ERROR_NOTDONE;
				} else {
					status = hdd_close(ocargs->chunkid);
				}
				break;
			case OP_READ:
				if (jstate==JSTATE_DISABLED) {
					status = MFS_ERROR_NOTDONE;
				} else {
					status = hdd_read(rdargs->chunkid,rdargs->version,rdargs->blocknum,rdargs->buffer,rdargs->offset,rdargs->size,rdargs->crcbuff);
				}
				break;
			case OP_WRITE:
				if (jstate==JSTATE_DISABLED) {
					status = MFS_ERROR_NOTDONE;
				} else {
					status = hdd_write(wrargs->chunkid,wrargs->version,wrargs->blocknum,wrargs->buffer,wrargs->offset,wrargs->size,wrargs->crcbuff);
				}
				break;
*/
			case OP_SERV_READ:
				if (jstate==JSTATE_DISABLED) {
					status = MFS_ERROR_NOTDONE;
				} else {
					status = mainserv_read(rwargs->sock,rwargs->packet,rwargs->length);
				}
				break;
			case OP_SERV_WRITE:
				if (jstate==JSTATE_DISABLED) {
					status = MFS_ERROR_NOTDONE;
				} else {
					status = mainserv_write(rwargs->sock,rwargs->packet,rwargs->length);
				}
				break;
			case OP_REPLICATE:
				if (jstate==JSTATE_DISABLED) {
					status = MFS_ERROR_NOTDONE;
				} else {
					status = replicate(rpargs->chunkid,rpargs->version,rpargs->xormasks,rpargs->srccnt,((uint8_t*)(jptr->args))+sizeof(chunk_rp_args));
				}
				break;
			case OP_GETBLOCKS:
				if (jstate==JSTATE_DISABLED) {
					status = MFS_ERROR_NOTDONE;
				} else {
					status = hdd_get_blocks(ijargs->chunkid,ijargs->version,ijargs->pointer);
				}
				break;
			case OP_GETCHECKSUM:
				if (jstate==JSTATE_DISABLED) {
					status = MFS_ERROR_NOTDONE;
				} else {
					status = hdd_get_checksum(ijargs->chunkid,ijargs->version,ijargs->pointer);
				}
				break;
			case OP_GETCHECKSUMTAB:
				if (jstate==JSTATE_DISABLED) {
					status = MFS_ERROR_NOTDONE;
				} else {
					status = hdd_get_checksum_tab(ijargs->chunkid,ijargs->version,ijargs->pointer);
				}
				break;
			case OP_CHUNKMOVE:
				if (jstate==JSTATE_DISABLED) {
					status = MFS_ERROR_NOTDONE;
				} else {
					status = hdd_move(mvargs->fsrc,mvargs->fdst);
				}
				break;
			default: // OP_EXIT
//				syslog(LOG_NOTICE,"worker %p exiting (jobqueue: %p)",(void*)pthread_self(),jp->jobqueue);
				zassert(pthread_mutex_lock(&(jp->jobslock)));
				job_close_worker(w);
				zassert(pthread_mutex_unlock(&(jp->jobslock)));
				return NULL;
		}
		job_send_status(jp,jobid,status);
		zassert(pthread_mutex_lock(&(jp->jobslock)));
		jp->workers_avail++;
		if (jp->workers_avail > jp->workers_max_idle) {
			job_close_worker(w);
			zassert(pthread_mutex_unlock(&(jp->jobslock)));
			return NULL;
		}
		zassert(pthread_mutex_unlock(&(jp->jobslock)));
	}
}

/**
 * job_new函数主要是新建一个job,主要处理流程是：
 * 分配一个job，
 * 设置jobid、callback、extra、args、jstate（JSTATE_ENABLED状态），
 * 并将该job连接到jobhash链表数组中，
 * 调用queue_put将该job加入到jobqueue队列中，
 * 调整jobpool的nextjobid++，
 * 返回jobid。
 * */
static inline uint32_t job_new(jobpool *jp,uint32_t op,void *args,void (*callback)(uint8_t status,void *extra),void *extra,uint8_t errstatus,uint8_t returnonfull) {
//	jobpool* jp = (jobpool*)jpool;
/*
	if (exiting) {
		if (callback) {
			callback(MFS_ERROR_NOTDONE,extra);
		}
		if (args) {
			free(args);
		}
		return 0;
	} else {
*/
		uint32_t jobid;
		uint32_t jhpos;
		job **jhandle,*jptr;

		jptr = malloc(sizeof(job));
		passert(jptr);

		zassert(pthread_mutex_lock(&(jp->jobslock)));
		jobid = jp->nextjobid;
		jp->nextjobid++;
		if (jp->nextjobid==0) {
			jp->nextjobid=1;
		}
		jhpos = JHASHPOS(jobid);
		jptr->jobid = jobid;
		jptr->callback = callback;
		jptr->extra = extra;
		jptr->args = args;
		jptr->jstate = JSTATE_ENABLED;
		jptr->next = jp->jobhash[jhpos];
		jp->jobhash[jhpos] = jptr;
		zassert(pthread_mutex_unlock(&(jp->jobslock)));
//		queue_put(jp->jobqueue,jobid,op,(uint8_t*)jptr,1);
		if (queue_tryput(jp->jobqueue,jobid,op,(uint8_t*)jptr,1)<0) {
			if (returnonfull) {
				// remove this job from data structures
				zassert(pthread_mutex_lock(&(jp->jobslock)));
				jhandle = jp->jobhash+jhpos;
				while ((jptr = *jhandle)) {
					if (jptr->jobid==jobid) {
						*jhandle = jptr->next;
						if (jptr->args) {
							free(jptr->args);
						}
						free(jptr);
						break;
					} else {
						jhandle = &(jptr->next);
					}
				}
				zassert(pthread_mutex_unlock(&(jp->jobslock)));
				// end return jobid==0
				return 0;
			} else {
				job_send_status(jp,jobid,errstatus);
			}
		}
		return jobid;
//	}
}

/* interface */

void* job_pool_new(uint32_t jobs) {
	int fd[2];
	uint32_t i;
	jobpool* jp;

	if (pipe(fd)<0) {
		return NULL;
	}
	jp=malloc(sizeof(jobpool));
	passert(jp);
//	syslog(LOG_WARNING,"new pool of workers (%p:%"PRIu8")",(void*)jp,workers);
	jp->rpipe = fd[0];
	jp->wpipe = fd[1];
	jp->workers_avail = 0;
	jp->workers_total = 0;
	jp->workers_term_waiting = 0;
	zassert(pthread_cond_init(&(jp->worker_term_cond),NULL));
	zassert(pthread_mutex_init(&(jp->pipelock),NULL));
	zassert(pthread_mutex_init(&(jp->jobslock),NULL));
	jp->jobqueue = queue_new(jobs);
//	syslog(LOG_WARNING,"new jobqueue: %p",jp->jobqueue);
	jp->statusqueue = queue_new(0);
	zassert(pthread_mutex_lock(&(jp->jobslock)));
	for (i=0 ; i<JHASHSIZE ; i++) {
		jp->jobhash[i]=NULL;
	}
	jp->nextjobid = 1;
	job_spawn_worker(jp);
	zassert(pthread_mutex_unlock(&(jp->jobslock)));
	return jp;
}

uint32_t job_pool_jobs_count(void) {
	jobpool* jp = globalpool;
	uint32_t res;
	zassert(pthread_mutex_lock(&(jp->jobslock)));
	res = (jp->workers_total - jp->workers_avail) + queue_elements(jp->jobqueue);
	zassert(pthread_mutex_unlock(&(jp->jobslock)));
	return res;
}

/*
void job_pool_disable_and_change_callback_all(void (*callback)(uint8_t status,void *extra)) {
	jobpool* jp = globalpool;
	uint32_t jhpos;
	job *jptr;

	zassert(pthread_mutex_lock(&(jp->jobslock)));
	for (jhpos = 0 ; jhpos<JHASHSIZE ; jhpos++) {
		for (jptr = jp->jobhash[jhpos] ; jptr ; jptr=jptr->next) {
			if (jptr->jstate==JSTATE_ENABLED) {
				jptr->jstate=JSTATE_DISABLED;
			}
			jptr->callback=callback;
		}
	}
	zassert(pthread_mutex_unlock(&(jp->jobslock)));
}
*/

void job_pool_disable_job(uint32_t jobid) {
	jobpool* jp = globalpool;
	uint32_t jhpos = JHASHPOS(jobid);
	job *jptr;

	zassert(pthread_mutex_lock(&(jp->jobslock)));
	for (jptr = jp->jobhash[jhpos] ; jptr ; jptr=jptr->next) {
		if (jptr->jobid==jobid) {
			if (jptr->jstate==JSTATE_ENABLED) {
				jptr->jstate=JSTATE_DISABLED;
			}
		}
	}
	zassert(pthread_mutex_unlock(&(jp->jobslock)));
}

void job_pool_change_callback(uint32_t jobid,void (*callback)(uint8_t status,void *extra),void *extra) {
	jobpool* jp = globalpool;
	uint32_t jhpos = JHASHPOS(jobid);
	job *jptr;

	zassert(pthread_mutex_lock(&(jp->jobslock)));
	for (jptr = jp->jobhash[jhpos] ; jptr ; jptr=jptr->next) {
		if (jptr->jobid==jobid) {
			jptr->callback=callback;
			jptr->extra=extra;
		}
	}
	zassert(pthread_mutex_unlock(&(jp->jobslock)));
}

void job_pool_check_jobs(uint8_t cb) {
	jobpool* jp = globalpool;
	uint32_t jobid,jhpos;
	uint8_t status;
	int notlast;
	job **jhandle,*jptr;

	zassert(pthread_mutex_lock(&(jp->jobslock)));
	do {
		notlast = job_receive_status(jp,&jobid,&status);
		jhpos = JHASHPOS(jobid);
		jhandle = jp->jobhash+jhpos;
		while ((jptr = *jhandle)) {
			if (jptr->jobid==jobid) {
				if (jptr->callback && cb) {
					jptr->callback(status,jptr->extra);
				}
				*jhandle = jptr->next;
				if (jptr->args) {
					free(jptr->args);
				}
				free(jptr);
				break;
			} else {
				jhandle = &(jptr->next);
			}
		}
	} while (notlast);
	zassert(pthread_mutex_unlock(&(jp->jobslock)));
}

void job_pool_delete(jobpool* jp) {
	queue_close(jp->jobqueue);
	zassert(pthread_mutex_lock(&(jp->jobslock)));
	while (jp->workers_total>0) {
		jp->workers_term_waiting++;
		zassert(pthread_cond_wait(&(jp->worker_term_cond),&(jp->jobslock)));
	}
	zassert(pthread_mutex_unlock(&(jp->jobslock)));
	if (!queue_isempty(jp->statusqueue)) {
		syslog(LOG_WARNING,"not empty job queue !!!");
		job_pool_check_jobs(0);
	}
//	syslog(LOG_NOTICE,"deleting jobqueue: %p",jp->jobqueue);
	queue_delete(jp->jobqueue);
	queue_delete(jp->statusqueue);
	zassert(pthread_cond_destroy(&(jp->worker_term_cond)));
	zassert(pthread_mutex_destroy(&(jp->pipelock)));
	zassert(pthread_mutex_destroy(&(jp->jobslock)));
	close(jp->rpipe);
	close(jp->wpipe);
	free(jp);
}

uint32_t job_inval(void (*callback)(uint8_t status,void *extra),void *extra) {
	jobpool* jp = globalpool;
	return job_new(jp,OP_INVAL,NULL,callback,extra,MFS_ERROR_EINVAL,0);
}

/*
uint32_t job_mainserv(int sock) {
	jobpool* jp = globalpool;
	int *args;
	args = malloc(sizeof(int));
	passert(args);
	*args = sock;
	return job_new(jp,OP_MAINSERV,args,NULL,NULL);
}
*/

uint32_t job_chunkop(void (*callback)(uint8_t status,void *extra),void *extra,uint64_t chunkid,uint32_t version,uint32_t newversion,uint64_t copychunkid,uint32_t copyversion,uint32_t length) {
	jobpool* jp = globalpool;
	chunk_op_args *args;
	args = malloc(sizeof(chunk_op_args));
	passert(args);
	args->chunkid = chunkid;
	args->version = version;
	args->newversion = newversion;
	args->copychunkid = copychunkid;
	args->copyversion = copyversion;
	args->length = length;
	return job_new(jp,OP_CHUNKOP,args,callback,extra,MFS_ERROR_NOTDONE,0);
}
/*
uint32_t job_open(void (*callback)(uint8_t status,void *extra),void *extra,uint64_t chunkid,uint32_t version) {
	jobpool* jp = globalpool;
	chunk_oc_args *args;
	args = malloc(sizeof(chunk_oc_args));
	passert(args);
	args->chunkid = chunkid;
	args->version = version;
	return job_new(jp,OP_OPEN,args,callback,extra);
}

uint32_t job_close(void (*callback)(uint8_t status,void *extra),void *extra,uint64_t chunkid) {
	jobpool* jp = globalpool;
	chunk_oc_args *args;
	args = malloc(sizeof(chunk_oc_args));
	passert(args);
	args->chunkid = chunkid;
	args->version = 0;
	return job_new(jp,OP_CLOSE,args,callback,extra);
}

uint32_t job_read(void (*callback)(uint8_t status,void *extra),void *extra,uint64_t chunkid,uint32_t version,uint16_t blocknum,uint8_t *buffer,uint32_t offset,uint32_t size,uint8_t *crcbuff) {
	jobpool* jp = globalpool;
	chunk_rd_args *args;
	args = malloc(sizeof(chunk_rd_args));
	passert(args);
	args->chunkid = chunkid;
	args->version = version;
	args->blocknum = blocknum;
	args->buffer = buffer;
	args->offset = offset;
	args->size = size;
	args->crcbuff = crcbuff;
	return job_new(jp,OP_READ,args,callback,extra);
}

uint32_t job_write(void (*callback)(uint8_t status,void *extra),void *extra,uint64_t chunkid,uint32_t version,uint16_t blocknum,const uint8_t *buffer,uint32_t offset,uint32_t size,const uint8_t *crcbuff) {
	jobpool* jp = globalpool;
	chunk_wr_args *args;
	args = malloc(sizeof(chunk_wr_args));
	passert(args);
	args->chunkid = chunkid;
	args->version = version;
	args->blocknum = blocknum;
	args->buffer = buffer;
	args->offset = offset;
	args->size = size;
	args->crcbuff = crcbuff;
	return job_new(jp,OP_WRITE,args,callback,extra);
}
*/

uint32_t job_serv_read(void (*callback)(uint8_t status,void *extra),void *extra,int sock,const uint8_t *packet,uint32_t length) {
	jobpool* jp = globalpool;
	chunk_rw_args *args;
	args = malloc(sizeof(chunk_rw_args));
	passert(args);
	args->sock = sock;
	args->packet = packet;
	args->length = length;
	return job_new(jp,OP_SERV_READ,args,callback,extra,0,1);
}
/**
 * 调用：job_serv_write(csserv_iothread_finished,eptr,eptr->sock,data,length);
 * callback = csserv_iothread_finished
 * extra = eptr
 * sock = eptr->sock
 * packet = data
 * length = length
 * */
uint32_t job_serv_write(void (*callback)(uint8_t status,void *extra),void *extra,int sock,const uint8_t *packet,uint32_t length) {
	//初始化chunk_rw_args对象
	jobpool* jp = globalpool;
	chunk_rw_args *args;
	args = malloc(sizeof(chunk_rw_args));
	passert(args);
	args->sock = sock;
	args->packet = packet;
	args->length = length;
	//往globalpool中添加一个新的job，返回一个jpbid
	return job_new(jp,OP_SERV_WRITE,args,callback,extra,0,1);
}

uint32_t job_replicate_raid(void (*callback)(uint8_t status,void *extra),void *extra,uint64_t chunkid,uint32_t version,uint8_t srccnt,const uint32_t xormasks[4],const uint8_t *srcs) {
	jobpool* jp = globalpool;
	chunk_rp_args *args;
	uint8_t *ptr;
	ptr = malloc(sizeof(chunk_rp_args)+srccnt*18);
	passert(ptr);
	args = (chunk_rp_args*)ptr;
	ptr += sizeof(chunk_rp_args);
	args->chunkid = chunkid;
	args->version = version;
	args->srccnt = srccnt;
	args->xormasks[0] = xormasks[0];
	args->xormasks[1] = xormasks[1];
	args->xormasks[2] = xormasks[2];
	args->xormasks[3] = xormasks[3];
	memcpy(ptr,srcs,srccnt*18);
	return job_new(jp,OP_REPLICATE,args,callback,extra,MFS_ERROR_NOTDONE,0);
}

uint32_t job_replicate_simple(void (*callback)(uint8_t status,void *extra),void *extra,uint64_t chunkid,uint32_t version,uint32_t ip,uint16_t port) {
	jobpool* jp = globalpool;
	chunk_rp_args *args;
	uint8_t *ptr;
	ptr = malloc(sizeof(chunk_rp_args)+18);
	passert(ptr);
	args = (chunk_rp_args*)ptr;
	ptr += sizeof(chunk_rp_args);
	args->chunkid = chunkid;
	args->version = version;
	args->srccnt = 1;
	args->xormasks[0] = UINT32_C(0x88888888);
	args->xormasks[1] = UINT32_C(0x44444444);
	args->xormasks[2] = UINT32_C(0x22222222);
	args->xormasks[3] = UINT32_C(0x11111111);
	put64bit(&ptr,chunkid);
	put32bit(&ptr,version);
	put32bit(&ptr,ip);
	put16bit(&ptr,port);
	return job_new(jp,OP_REPLICATE,args,callback,extra,MFS_ERROR_NOTDONE,0);
}

uint32_t job_get_chunk_blocks(void (*callback)(uint8_t status,void *extra),void *extra,uint64_t chunkid,uint32_t version,uint8_t *blocks) {
	jobpool* jp = globalpool;
	chunk_ij_args *args;
	args = malloc(sizeof(chunk_ij_args));
	passert(args);
	args->chunkid = chunkid;
	args->version = version;
	args->pointer = blocks;
	return job_new(jp,OP_GETBLOCKS,args,callback,extra,MFS_ERROR_NOTDONE,0);
}

uint32_t job_get_chunk_checksum(void (*callback)(uint8_t status,void *extra),void *extra,uint64_t chunkid,uint32_t version,uint8_t *checksum) {
	jobpool* jp = globalpool;
	chunk_ij_args *args;
	args = malloc(sizeof(chunk_ij_args));
	passert(args);
	args->chunkid = chunkid;
	args->version = version;
	args->pointer = checksum;
	return job_new(jp,OP_GETCHECKSUM,args,callback,extra,MFS_ERROR_NOTDONE,0);
}

uint32_t job_get_chunk_checksum_tab(void (*callback)(uint8_t status,void *extra),void *extra,uint64_t chunkid,uint32_t version,uint8_t *checksum_tab) {
	jobpool* jp = globalpool;
	chunk_ij_args *args;
	args = malloc(sizeof(chunk_ij_args));
	passert(args);
	args->chunkid = chunkid;
	args->version = version;
	args->pointer = checksum_tab;
	return job_new(jp,OP_GETCHECKSUMTAB,args,callback,extra,MFS_ERROR_NOTDONE,0);
}

uint32_t job_chunk_move(void (*callback)(uint8_t status,void *extra),void *extra,void *fsrc,void *fdst) {
	jobpool* jp = globalpool;
	chunk_mv_args *args;
	args = malloc(sizeof(chunk_mv_args));
	passert(args);
	args->fsrc = fsrc;
	args->fdst = fdst;
	return job_new(jp,OP_CHUNKMOVE,args,callback,extra,MFS_ERROR_NOTDONE,0);
}

void job_desc(struct pollfd *pdesc,uint32_t *ndesc) {
	uint32_t pos = *ndesc;
	jobpool* jp = globalpool;

	pdesc[pos].fd = jp->rpipe;
	pdesc[pos].events = POLLIN;
	jp->fdpdescpos = pos;
	pos++;

	*ndesc = pos;
}

void job_serve(struct pollfd *pdesc) {
	jobpool* jp = globalpool;
	uint32_t jobscnt;

	if (jp->fdpdescpos>=0 && (pdesc[jp->fdpdescpos].revents & POLLIN)) {
		job_pool_check_jobs(1);
	}

	jobscnt = job_pool_jobs_count();
	if (jobscnt>=stats_maxjobscnt) {
		stats_maxjobscnt=jobscnt;
	}
}

void job_heavyload_test(void) {
	jobpool* jp = globalpool;
	uint8_t hlstatus = 0;
	uint32_t load = 0; // make stupid gcc happy

	zassert(pthread_mutex_lock(&(jp->jobslock)));
	if (jp->workers_total - jp->workers_avail > jp->workers_himark) {
		hlstatus = 2;
	}
	if (jp->workers_total - jp->workers_avail < jp->workers_lomark) {
		hlstatus = 1;
	}
	if (hlstatus) {
		load = (jp->workers_total - jp->workers_avail) + queue_elements(jp->jobqueue);
	}
	zassert(pthread_mutex_unlock(&(jp->jobslock)));

	if (hlstatus) {
		masterconn_heavyload(load,hlstatus);
	}
}

//void job_wantexit(void) {
//	exiting = 1;
//}

int job_canexit(void) {
	return (job_pool_jobs_count()>0)?0:1;
}

void job_term(void) {
	job_pool_delete(globalpool);
}

void job_reload(void) {
	jobpool* jp = globalpool;

	zassert(pthread_mutex_lock(&(jp->jobslock)));

	jp->workers_max = cfg_getuint32("WORKERS_MAX",250);
	jp->workers_himark = (jp->workers_max * 3) / 4;
	jp->workers_lomark = (jp->workers_max * 2) / 4;
	jp->workers_max_idle = cfg_getuint32("WORKERS_MAX_IDLE",40);

	zassert(pthread_mutex_unlock(&(jp->jobslock)));
}

int job_init(void) {
//	globalpool = (jobpool*)malloc(sizeof(jobpool));
//	exiting = 0;
	globalpool = job_pool_new(cfg_getuint32("WORKERS_QUEUE_LENGTH",250)); // deprecated option

	if (globalpool==NULL) {
		return -1;
	}
	job_reload();

	main_destruct_register(job_term);
//	main_wantexit_register(job_wantexit);
	main_canexit_register(job_canexit);
	main_reload_register(job_reload);
	main_eachloop_register(job_heavyload_test);
	main_poll_register(job_desc,job_serve);
	return 0;
}
