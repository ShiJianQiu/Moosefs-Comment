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

#if defined(_THREAD_SAFE) || defined(_REENTRANT) || defined(_USE_PTHREADS)
#  define USE_PTHREADS 1    //多线程
#endif

#ifndef MFSMAXFILES
#define MFSMAXFILES 4096
#endif

#if defined(HAVE_MLOCKALL)
#  if defined(HAVE_SYS_MMAN_H)
#    include <sys/mman.h>
#  endif
#  if defined(HAVE_SYS_RESOURCE_H)
#    include <sys/resource.h>
#  endif
#  if defined(RLIMIT_MEMLOCK) && defined(MCL_CURRENT) && defined(MCL_FUTURE)
#    define MFS_USE_MEMLOCK 1
#  endif
#endif

#if defined(HAVE_MALLOC_H)
#  include <malloc.h>
#endif

#if defined(HAVE_LINUX_OOM_H)
#  include <linux/oom.h>
#  if defined(OOM_DISABLE) || defined(OOM_SCORE_ADJ_MIN)
#    define OOM_ADJUSTABLE 1
#  endif
#endif

#if defined(HAVE_SYS_PRCTL_H)
#  include <sys/prctl.h>
#endif

#include <sys/stat.h>
#include <sys/wait.h>
#include <sys/types.h>
#include <sys/time.h>

#include <signal.h>
#include <fcntl.h>
#include <unistd.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <syslog.h>
#include <string.h>
#include <strings.h>
#include <time.h>
#include <sys/resource.h>
#include <grp.h>
#include <pwd.h>
#ifdef USE_PTHREADS
#include <pthread.h>
#endif

#define STR_AUX(x) #x
#define STR(x) STR_AUX(x)

#include "main.h"
#include "clocks.h"
#include "sockets.h"
#include "cfg.h"
#include "strerr.h"
#include "crc.h"
#include "init.h"
#include "massert.h"
#include "slogger.h"
#include "portable.h"
#include "processname.h"

#define RM_RESTART 0
#define RM_START 1
#define RM_STOP 2
#define RM_RELOAD 3
#define RM_INFO 4
#define RM_TEST 5
#define RM_KILL 6
#define RM_TRY_RESTART 7
#define RM_RESTORE 8

typedef struct deentry {
	void (*fun)(void);
	struct deentry *next;
} deentry;

static deentry *dehead=NULL;


typedef struct weentry {
	void (*fun)(void);
	struct weentry *next;
} weentry;

static weentry *wehead=NULL;


typedef struct ceentry {
	int (*fun)(void);
	struct ceentry *next;
} ceentry;

static ceentry *cehead=NULL;


typedef struct rlentry {
	void (*fun)(void);
	struct rlentry *next;
} rlentry;

static rlentry *rlhead=NULL;


typedef struct inentry {
	void (*fun)(void);
	struct inentry *next;
} inentry;

static inentry *inhead=NULL;


typedef struct kaentry {
	void (*fun)(void);
	struct kaentry *next;
} kaentry;

static kaentry *kahead=NULL;


typedef struct pollentry {
	/*
	desc主要完成的工作是向一个pollfd类型的数组填充被监视的文件描述符fd和设置监控事件
	（主要包括两类描述符，
	一类是一个本地socket描述符用于监听是否有新的链接需要建立，
	另一类是已经建立的socket链接描述符用于进行消息交互）,并累加和返回文件描述符个数；
	*/
	void (*desc)(struct pollfd *,uint32_t *);
	/*
	serve主要工作就是依据文件描述符的状态做相应处理
	（具体是，对于本地socket描述符，如果有读请求，则建立一个新的socket描述符用于链接并加入到第二类描述符链表中；
	对于已建立链接的每个socket描述符都先接受消息请求数据，然后处理，最后发送响应数据）。
	*/
	void (*serve)(struct pollfd *);
	struct pollentry *next;
} pollentry;

static pollentry *pollhead=NULL;


typedef struct eloopentry {
	void (*fun)(void);
	struct eloopentry *next;
} eloopentry;

static eloopentry *eloophead=NULL;


typedef struct chldentry {
	pid_t pid;
	void (*fun)(int);
	struct chldentry *next;
} chldentry;

static chldentry *chldhead=NULL;


typedef struct timeentry {
	uint64_t nextevent;
	uint64_t useconds;
	uint64_t usecoffset;
	void (*fun)(void);
	struct timeentry *next;
} timeentry;

static timeentry *timehead=NULL;

#ifdef USE_PTHREADS
static pthread_mutex_t nowlock = PTHREAD_MUTEX_INITIALIZER;
#endif
static uint32_t now;		//now=time(NULL)获取系统时间，单位为秒;
static uint64_t usecnow;
//static int alcnt=0;

static int signalpipe[2];

/* interface */

/**
 * 向dehead链表注册函数，完成诸如向磁盘写元数据文件，释放与其他节点的链接，释放内存资源等工作。
 * */
void main_destruct_register (void (*fun)(void)) {
	deentry *aux=(deentry*)malloc(sizeof(deentry));
	passert(aux);
	aux->fun = fun;
	aux->next = dehead;
	dehead = aux;
}

/**
 * 向cehead链表注册函数，比如通知chunkserver停止向client读写数据。
 * */
void main_canexit_register (int (*fun)(void)) {
	ceentry *aux=(ceentry*)malloc(sizeof(ceentry));
	passert(aux);
	aux->fun = fun;
	aux->next = cehead;
	cehead = aux;
}

/**
 * 向wehead链表注册函数，告诉client用户端master这边需要终止进程，一些正在进行的数据传输需要终止。
 * */
void main_wantexit_register (void (*fun)(void)) {
	weentry *aux=(weentry*)malloc(sizeof(weentry));
	passert(aux);
	aux->fun = fun;
	aux->next = wehead;
	wehead = aux;
}

/**
 * 向reload rlhead链表注册函数。主要是在重新加载配置文件时会调用。
 * 比如我们修改了master的/etc/mfsexports文件，然后执行mfsmaster reload命令，启动一个进程，
 * 在本进程的main函数中就会向先前运行的mfsmaster进程发送SIGHUP信号。
 * 而先前mfsmaster进程对于SIGHUP的信号处理函数是将一个全局变量reload置1，
 * 在mainloop如果发现reload=1,则遍历调用rlhead链表中的每个fun，重新加载配置文件，之后恢复reload为0。
 * */
void main_reload_register (void (*fun)(void)) {
	rlentry *aux=(rlentry*)malloc(sizeof(rlentry));
	passert(aux);
	aux->fun = fun;
	aux->next = rlhead;
	rlhead = aux;
}

/**
 * 向inhead链表注册函数
 * */
void main_info_register (void (*fun)(void)) {
	inentry *aux=(inentry*)malloc(sizeof(inentry));
	passert(aux);
	aux->fun = fun;
	aux->next = inhead;
	inhead = aux;
}

/**
 * 向kahead链表注册函数，完成keepalive任务
 * */
void main_keepalive_register (void (*fun)(void)) {
	kaentry *aux=(kaentry*)malloc(sizeof(kaentry));
	passert(aux);
	aux->fun = fun;
	aux->next = kahead;
	kahead = aux;
}

/**
 * 向pollhead链表中注册函数。它的链表函数主要完成的工作是与其他节点建立连接并进行消息接收和发生以完成具体的任务。
 * */
void main_poll_register (void (*desc)(struct pollfd *,uint32_t *),void (*serve)(struct pollfd *)) {
	pollentry *aux=(pollentry*)malloc(sizeof(pollentry));
	passert(aux);
	aux->desc = desc;
	aux->serve = serve;
	aux->next = pollhead;
	pollhead = aux;
}

/**
 * 向eloophead链表中注册函数，eloophead函数链表中的函数是指每次mainloop循环都会执行的函数，它比timeentry更简单，没有时间周期限制。
 * */
void main_eachloop_register (void (*fun)(void)) {
	eloopentry *aux=(eloopentry*)malloc(sizeof(eloopentry));
	passert(aux);
	aux->fun = fun;
	aux->next = eloophead;
	eloophead = aux;
}

void main_chld_register (pid_t pid,void (*fun)(int)) {
	chldentry *aux=(chldentry*)malloc(sizeof(chldentry));
	passert(aux);
	aux->fun = fun;
	aux->pid = pid;
	aux->next = chldhead;
	chldhead = aux;
}
//对应1.6的main_timeregister
void* main_msectime_register (uint32_t mseconds,uint32_t offset,void (*fun)(void)) {
	timeentry *aux;
	uint64_t useconds = UINT64_C(1000) * (uint64_t)mseconds;
	uint64_t usecoffset = UINT64_C(1000) * (uint64_t)offset;
	if (useconds==0 || usecoffset>=useconds) {
		return NULL;
	}
	aux = (timeentry*)malloc(sizeof(timeentry));
	passert(aux);
	aux->nextevent = (((usecnow / useconds) * useconds) + usecoffset);
	while (aux->nextevent<usecnow) {
		aux->nextevent+=useconds;
	}
	aux->useconds = useconds;
	aux->usecoffset = usecoffset;
	aux->fun = fun;
	aux->next = timehead;
	timehead = aux;
	return aux;
}

int main_msectime_change(void* x,uint32_t mseconds,uint32_t offset) {
	timeentry *aux = (timeentry*)x;
	uint64_t useconds = UINT64_C(1000) * (uint64_t)mseconds;
	uint64_t usecoffset = UINT64_C(1000) * (uint64_t)offset;
	if (useconds==0 || usecoffset>=useconds) {
		return -1;
	}
	aux->nextevent = (((usecnow / useconds) * useconds) + usecoffset);
	while (aux->nextevent<usecnow) {
		aux->nextevent+=useconds;
	}
	aux->useconds = useconds;
	aux->usecoffset = usecoffset;
	return 0;
}

/**
 * 向timehead链表中注册函数，timehead函数链表中的函数的执行是有时间周期限制的。timeentry中的fun即是要定期执行的函数。
 * timeentry中的seconds是时间周期，单位是秒。
 * 但实际上，因为并没有用到定时器中断等定时机制来执行这些函数，而仅仅是在mainloop中循环执行，所以这个周期是不精确。
 * */
void* main_time_register (uint32_t seconds,uint32_t offset,void (*fun)(void)) {
	return main_msectime_register(1000*seconds,1000*offset,fun);
/*	timeentry *aux;
	if (seconds==0 || offset>=seconds) {
		return NULL;
	}
	aux = (timeentry*)malloc(sizeof(timeentry));
	passert(aux);
	aux->nextevent = (((now / seconds) * seconds) + offset);
	while (aux->nextevent<now) {
		aux->nextevent+=seconds;
	}
	aux->seconds = seconds;
	aux->offset = offset;
	aux->mode = mode;
	aux->fun = fun;
	aux->next = timehead;
	timehead = aux;
	return aux;
*/
}

int main_time_change(void* x,uint32_t seconds,uint32_t offset) {
	return main_msectime_change(x,1000*seconds,1000*offset);
/*	timeentry *aux = (timeentry*)x;
	if (seconds==0 || offset>=seconds) {
		return -1;
	}
	aux->nextevent = ((now / seconds) * seconds) + offset;
	while (aux->nextevent<now) {
		aux->nextevent+=seconds;
	}
	aux->seconds = seconds;
	aux->offset = offset;
	aux->mode = mode;
	return 0;
*/
}

/* internal */

void free_all_registered_entries(void) {
	deentry *de,*den;
	ceentry *ce,*cen;
	weentry *we,*wen;
	rlentry *re,*ren;
	inentry *ie,*ien;
	pollentry *pe,*pen;
	eloopentry *ee,*een;
	timeentry *te,*ten;

	for (de = dehead ; de ; de = den) {
		den = de->next;
		free(de);
	}

	for (ce = cehead ; ce ; ce = cen) {
		cen = ce->next;
		free(ce);
	}

	for (we = wehead ; we ; we = wen) {
		wen = we->next;
		free(we);
	}

	for (re = rlhead ; re ; re = ren) {
		ren = re->next;
		free(re);
	}

	for (ie = inhead ; ie ; ie = ien) {
		ien = ie->next;
		free(ie);
	}

	for (pe = pollhead ; pe ; pe = pen) {
		pen = pe->next;
		free(pe);
	}

	for (ee = eloophead ; ee ; ee = een) {
		een = ee->next;
		free(ee);
	}

	for (te = timehead ; te ; te = ten) {
		ten = te->next;
		free(te);
	}
}

int canexit(void) {
	ceentry *aux;
	for (aux = cehead ; aux!=NULL ; aux=aux->next ) {
		if (aux->fun()==0) {
			return 0;
		}
	}
	return 1;
}

uint32_t main_time(void) {
#ifdef USE_PTHREADS
	uint32_t ret;
	zassert(pthread_mutex_lock(&nowlock));
	ret = now;
	zassert(pthread_mutex_unlock(&nowlock));
	return ret;
#else
	return now;
#endif
}

uint64_t main_utime(void) {
	struct timeval tv;
	uint64_t usec;

	gettimeofday(&tv,NULL);
	usec = tv.tv_sec;
	usec *= 1000000;
	usec += tv.tv_usec;
	return usec;
}

static inline void destruct(void) {
	deentry *deit;
	for (deit = dehead ; deit!=NULL ; deit=deit->next ) {
		deit->fun();
	}
}

void main_keep_alive(void) {
	uint64_t useclast;
	struct timeval tv;
	kaentry *kait;

	gettimeofday(&tv,NULL);
	useclast = usecnow;
	usecnow = tv.tv_sec;
	usecnow *= 1000000;
	usecnow += tv.tv_usec;
#ifdef USE_PTHREADS
	zassert(pthread_mutex_lock(&nowlock));
#endif
	now = tv.tv_sec;
#ifdef USE_PTHREADS
	zassert(pthread_mutex_unlock(&nowlock));
#endif
	if (usecnow>useclast && useclast>0) {
		useclast = usecnow - useclast;
	} else {
		useclast = 0;
	}
	if (useclast > 5000000) {
		syslog(LOG_WARNING,"long loop detected (%"PRIu64".%06"PRIu32"s)",useclast/1000000,(uint32_t)(useclast%1000000));
	}

	for (kait = kahead ; kait!=NULL ; kait=kait->next ) {
		kait->fun();
	}
}

void mainloop() {
	uint64_t prevtime = 0;
	uint64_t useclast;
	struct timeval tv;
	pollentry *pollit;
	eloopentry *eloopit;
	timeentry *timeit;
	ceentry *ceit;
	weentry *weit;
	rlentry *rlit;
	inentry *init;
	//pdesc
	struct pollfd pdesc[MFSMAXFILES];
	uint32_t ndesc;//记录描述符个数
	int i;
	int t,r;

	/**
	  首先遍历pollhead链表，依次调用每一个pollentry的desc函数，
	  完成向pdesc填充描述符，并用ndesc记录描述符个数，然后调用poll，监听所有描述符的是否有I/O请求，
	  如果有则遍历pollhead链表，依次调用每一个pollentry的serve函数处理I/O请求；
	  如果没有则根据返回的错误判断是否重试poll或者退出mainloop亦或者继续执行下面的代码。
	*/
	t = 0;
	r = 0;
	while (t!=3) {
		ndesc=1;
		pdesc[0].fd = signalpipe[0];
		pdesc[0].events = POLLIN;
		pdesc[0].revents = 0;
		for (pollit = pollhead ; pollit != NULL ; pollit = pollit->next) {
			//依次调用每一个pollentry的desc函数
			pollit->desc(pdesc,&ndesc);
		}
		//监听所有描述符的是否有I/O请求
		i = poll(pdesc,ndesc,10);
		gettimeofday(&tv,NULL);
		useclast = usecnow;
		usecnow = tv.tv_sec;
		usecnow *= 1000000;
		usecnow += tv.tv_usec;
#ifdef USE_PTHREADS
		zassert(pthread_mutex_lock(&nowlock));
#endif
		now = tv.tv_sec;
#ifdef USE_PTHREADS
		zassert(pthread_mutex_unlock(&nowlock));
#endif
		if (usecnow>useclast && useclast>0) {
			useclast = usecnow - useclast;
		} else {
			useclast = 0;
		}
		if (useclast > 5000000) {
			syslog(LOG_WARNING,"long loop detected (%"PRIu64".%06"PRIu32"s)",useclast/1000000,(uint32_t)(useclast%1000000));
		}
		if (i<0) {
			//如果没有则根据返回的错误判断是否重试poll或者退出mainloop亦或者继续执行下面的代码。
			if (!ERRNO_ERROR) {
				syslog(LOG_WARNING,"poll returned EAGAIN");
				portable_usleep(10000);
				continue;
			}
			if (errno!=EINTR) {
				syslog(LOG_WARNING,"poll error: %s",strerr(errno));
				break;
			}
		} else {
			//如果有则遍历pollhead链表 
			if ((pdesc[0].revents)&POLLIN) {
				uint8_t sigid;
				if (read(signalpipe[0],&sigid,1)==1) {
					if (sigid=='\001' && t==0) {
						syslog(LOG_NOTICE,"terminate signal received");
						t = 1;
					} else if (sigid=='\002') {
						syslog(LOG_NOTICE,"reloading config files");
						r = 1;
					} else if (sigid=='\003') {
						syslog(LOG_NOTICE,"child finished");
						r = 2;
					} else if (sigid=='\004') {
						syslog(LOG_NOTICE,"log extra info");
						r = 3;
					} else if (sigid=='\005') {
						syslog(LOG_NOTICE,"unexpected alarm/prof signal received - ignoring");
					} else if (sigid=='\006') {
						syslog(LOG_NOTICE,"internal terminate request");
						t = 1;
					}
				}
			}
			//依次调用每一个pollentry的serve函数处理I/O请求
			for (pollit = pollhead ; pollit != NULL ; pollit = pollit->next) {
				pollit->serve(pdesc);
			}
		}
		for (eloopit = eloophead ; eloopit != NULL ; eloopit = eloopit->next) {
			eloopit->fun();
		}
		if (usecnow<prevtime) {
			// time went backward !!! - recalculate "nextevent" time
			// adding previous_time_to_run prevents from running next event too soon.
			for (timeit = timehead ; timeit != NULL ; timeit = timeit->next) {
				uint64_t previous_time_to_run = timeit->nextevent - prevtime;
				if (previous_time_to_run > timeit->useconds) {
					previous_time_to_run = timeit->useconds;
				}
				timeit->nextevent = ((usecnow / timeit->useconds) * timeit->useconds) + timeit->usecoffset;
				while (timeit->nextevent <= usecnow+previous_time_to_run) {
					timeit->nextevent += timeit->useconds;
				}
			}
		} else if (usecnow>prevtime+UINT64_C(5000000)) {
			// time went forward !!! - just recalculate "nextevent" time
			for (timeit = timehead ; timeit != NULL ; timeit = timeit->next) {
				timeit->nextevent = ((usecnow / timeit->useconds) * timeit->useconds) + timeit->usecoffset;
				while (usecnow >= timeit->nextevent) {
					timeit->nextevent += timeit->useconds;
				}
			}
		}
		for (timeit = timehead ; timeit != NULL ; timeit = timeit->next) {
			if (usecnow >= timeit->nextevent) {
				uint32_t eventcounter = 0;
				while (usecnow >= timeit->nextevent && eventcounter<10) { // do not run more than 10 late entries
					timeit->fun();
					timeit->nextevent += timeit->useconds;
					eventcounter++;
				}
				if (usecnow >= timeit->nextevent) {
					timeit->nextevent = ((usecnow / timeit->useconds) * timeit->useconds) + timeit->usecoffset;
					while (usecnow >= timeit->nextevent) {
						timeit->nextevent += timeit->useconds;
					}
				}
			}
		}
		prevtime = usecnow;
		if (r==2) {
			chldentry *chldit,**chldptr;
			pid_t pid;
			int status;

			while ( (pid = waitpid(-1,&status,WNOHANG)) > 0) {
				chldptr = &chldhead;
				while ((chldit = *chldptr)) {
					if (chldit->pid == pid) {
						chldit->fun(status);
						*chldptr = chldit->next;
						free(chldit);
					} else {
						chldptr = &(chldit->next);
					}
				}
			}
			r = 0;
		}
		if (t==0) {
			if (r==1) {
				cfg_reload();
				for (rlit = rlhead ; rlit!=NULL ; rlit=rlit->next ) {
					rlit->fun();
				}
				r = 0;
			} else if (r==3) {
				for (init = inhead ; init!=NULL ; init=init->next ) {
					init->fun();
				}
				r = 0;
			}
		}
		if (t==1) {
			for (weit = wehead ; weit!=NULL ; weit=weit->next ) {
				weit->fun();
			}
			t = 2;
		}
		if (t==2) {
			i = 1;
			for (ceit = cehead ; ceit!=NULL && i ; ceit=ceit->next ) {
				if (ceit->fun()==0) {
					i=0;
				}
			}
			if (i) {
				t = 3;
			}
		}
	}
}

//判断是否初始化成功
int initialize(void) {
	uint32_t i;
	int ok;
	ok = 1;
	for (i=0 ; (long int)(RunTab[i].fn)!=0 && ok ; i++) {
#ifdef USE_PTHREADS
		zassert(pthread_mutex_lock(&nowlock));
#endif
		now = time(NULL);
#ifdef USE_PTHREADS
		zassert(pthread_mutex_unlock(&nowlock));
#endif
		if (RunTab[i].fn()<0) {
			mfs_arg_syslog(LOG_ERR,"init: %s failed !!!",RunTab[i].name);
			ok=0;
		}
	}
	return ok;
}

int restore(void) {
	uint32_t i;
	int ok;
	ok = 1;
	for (i=0 ; (long int)(RestoreRunTab[i].fn)!=0 && ok ; i++) {
#ifdef USE_PTHREADS
		zassert(pthread_mutex_lock(&nowlock));
#endif
		now = time(NULL);
#ifdef USE_PTHREADS
		zassert(pthread_mutex_unlock(&nowlock));
#endif
		if (RestoreRunTab[i].fn()<0) {
			mfs_arg_syslog(LOG_ERR,"restore: %s failed !!!",RestoreRunTab[i].name);
			ok=0;
		}
	}
	return ok;
}

int initialize_late(void) {
	uint32_t i;
	int ok;
	ok = 1;
	for (i=0 ; (long int)(LateRunTab[i].fn)!=0 && ok ; i++) {
#ifdef USE_PTHREADS
		zassert(pthread_mutex_lock(&nowlock));
#endif
		now = time(NULL);
#ifdef USE_PTHREADS
		zassert(pthread_mutex_unlock(&nowlock));
#endif
		if (LateRunTab[i].fn()<0) {
			mfs_arg_syslog(LOG_ERR,"init: %s failed !!!",LateRunTab[i].name);
			ok=0;
		}
	}
#ifdef USE_PTHREADS
	zassert(pthread_mutex_lock(&nowlock));
#endif
	now = time(NULL);
#ifdef USE_PTHREADS
	zassert(pthread_mutex_unlock(&nowlock));
#endif
	return ok;
}



/* signals */

static int termsignal[]={
	SIGTERM,
	-1
};

static int reloadsignal[]={
	SIGHUP,
	-1
};

static int infosignal[]={
#ifdef SIGINFO
	SIGINFO,
#endif
#ifdef SIGUSR1
	SIGUSR1,
#endif
	-1
};

static int chldsignal[]={
#ifdef SIGCHLD
	SIGCHLD,
#endif
#ifdef SIGCLD
	SIGCLD,
#endif
	-1
};

static int ignoresignal[]={
	SIGQUIT,
#ifdef SIGPIPE
	SIGPIPE,
#endif
#ifdef SIGTSTP
	SIGTSTP,
#endif
#ifdef SIGTTIN
	SIGTTIN,
#endif
#ifdef SIGTTOU
	SIGTTOU,
#endif
#ifdef SIGUSR2
	SIGUSR2,
#endif
	-1
};

static int alarmsignal[]={
#ifndef GPERFTOOLS
#ifdef SIGALRM
	SIGALRM,
#endif
#ifdef SIGVTALRM
	SIGVTALRM,
#endif
#ifdef SIGPROF
	SIGPROF,
#endif
#endif
	-1
};

static int daemonignoresignal[]={
	SIGINT,
	-1
};

void termhandle(int signo) {
	signo = write(signalpipe[1],"\001",1); // killing two birds with one stone - use signo and do something with value returned by write :)
	(void)signo; // and then use this value to calm down compiler ;)
}

void reloadhandle(int signo) {
	signo = write(signalpipe[1],"\002",1); // see above
	(void)signo;
}

void chldhandle(int signo) {
	signo = write(signalpipe[1],"\003",1); // see above
	(void)signo;
}

void infohandle(int signo) {
	signo = write(signalpipe[1],"\004",1); // see above
	(void)signo;
}

void alarmhandle(int signo) {
	signo = write(signalpipe[1],"\005",1); // see above
	(void)signo;
}

void set_signal_handlers(int daemonflag) {
	struct sigaction sa;
	uint32_t i;

	zassert(pipe(signalpipe));

#ifdef SA_RESTART
	sa.sa_flags = SA_RESTART;
#else
	sa.sa_flags = 0;
#endif
	sigemptyset(&sa.sa_mask);

	sa.sa_handler = termhandle;
	for (i=0 ; termsignal[i]>0 ; i++) {
		//sigaction，可以用来查询或设置信号处理方式。
		sigaction(termsignal[i],&sa,(struct sigaction *)0);
	}
	sa.sa_handler = reloadhandle;
	for (i=0 ; reloadsignal[i]>0 ; i++) {
		sigaction(reloadsignal[i],&sa,(struct sigaction *)0);
	}
	sa.sa_handler = infohandle;
	for (i=0 ; infosignal[i]>0 ; i++) {
		sigaction(infosignal[i],&sa,(struct sigaction *)0);
	}
	sa.sa_handler = alarmhandle;
	for (i=0 ; alarmsignal[i]>0 ; i++) {
		sigaction(alarmsignal[i],&sa,(struct sigaction *)0);
	}
	sa.sa_handler = chldhandle;
	for (i=0 ; chldsignal[i]>0 ; i++) {
		sigaction(chldsignal[i],&sa,(struct sigaction *)0);
	}
	sa.sa_handler = SIG_IGN;
	for (i=0 ; ignoresignal[i]>0 ; i++) {
		sigaction(ignoresignal[i],&sa,(struct sigaction *)0);
	}
	sa.sa_handler = daemonflag?SIG_IGN:termhandle;
	for (i=0 ; daemonignoresignal[i]>0 ; i++) {
		sigaction(daemonignoresignal[i],&sa,(struct sigaction *)0);
	}
}

void main_exit(void) {
	int i;
	i = write(signalpipe[1],"\006",1);
	(void)i;
}

void signal_cleanup(void) {
	close(signalpipe[0]);
	close(signalpipe[1]);
}

//改变uid，获取/修改权限
void changeugid(void) {
	char pwdgrpbuff[16384];
	struct passwd pwd,*pw;
	struct group grp,*gr;
	char *wuser;
	char *wgroup;
	uid_t wrk_uid;
	gid_t wrk_gid;
	int gidok;

	//getuid() :  函数返回一个调用程序的真实用户ID。表明当前运行位置程序的执行者。
	//geteuid(): 函数返回返回一个有效用户的ID。（EUID）是你最初执行程序时所用的ID，该ID是程序的所有者。
	//返回有效的用户识别码。root的uid值（0）
	//如果是root用户
	if (geteuid()==0) {
		wuser = cfg_getstr("WORKING_USER",DEFAULT_USER);
		wgroup = cfg_getstr("WORKING_GROUP",DEFAULT_GROUP);

		gidok = 0;
		wrk_gid = -1;
		if (wgroup[0]=='#') {
			wrk_gid = strtol(wgroup+1,NULL,10);
			gidok = 1;
		} else if (wgroup[0]) {
			if (getgrnam_r(wgroup,&grp,pwdgrpbuff,16384,&gr)!=0) {
				gr = NULL;
			}
			if (gr==NULL) {
				mfs_arg_syslog(LOG_WARNING,"%s: no such group !!!",wgroup);
				exit(1);
			}
			wrk_gid = gr->gr_gid;
			gidok = 1;
		}

		if (wuser[0]=='#') {
			wrk_uid = strtol(wuser+1,NULL,10);
			if (gidok==0) {
				getpwuid_r(wrk_uid,&pwd,pwdgrpbuff,16384,&pw);
				if (pw==NULL) {
					mfs_arg_syslog(LOG_ERR,"%s: no such user id - can't obtain group id",wuser+1);
					exit(1);
				}
				wrk_gid = pw->pw_gid;
			}
		} else {
			if (getpwnam_r(wuser,&pwd,pwdgrpbuff,16384,&pw)!=0) {
				pw = NULL;
			}
			if (pw==NULL) {
				mfs_arg_syslog(LOG_ERR,"%s: no such user !!!",wuser);
				exit(1);
			}
			wrk_uid = pw->pw_uid;
			if (gidok==0) {
				wrk_gid = pw->pw_gid;
			}
		}
		free(wuser);
		free(wgroup);

		if (setgid(wrk_gid)<0) {
			mfs_arg_errlog(LOG_ERR,"can't set gid to %d",(int)wrk_gid);
			exit(1);
		} else {
			syslog(LOG_NOTICE,"set gid to %d",(int)wrk_gid);
		}
		//setuid
		//(1)如果由普通用户调用,将当前进程的有效ID设置为uid.
		//(2)如果由有效用户ID符为0的进程调用,则将真实,有效和已保存用户ID都设置为uid.
		if (setuid(wrk_uid)<0) {
			mfs_arg_errlog(LOG_ERR,"can't set uid to %d",(int)wrk_uid);
			exit(1);
		} else {
			syslog(LOG_NOTICE,"set uid to %d",(int)wrk_uid);
		}
	}
}

static int lfd = -1;	// main lock

pid_t mylock(int fd) {
	struct flock fl;
	fl.l_start = 0;
	fl.l_len = 0;
	fl.l_pid = getpid();
	fl.l_type = F_WRLCK;
	fl.l_whence = SEEK_SET;
	for (;;) {
		if (fcntl(fd,F_SETLK,&fl)>=0) {	// lock set
			return 0;	// ok
		}
		if (ERRNO_ERROR) {	// error other than "already locked"
			return -1;	// error
		}
		if (fcntl(fd,F_GETLK,&fl)<0) {	// get lock owner
			return -1;	// error getting lock
		}
		if (fl.l_type!=F_UNLCK) {	// found lock
			return fl.l_pid;	// return lock owner
		}
	}
	return -1;	// pro forma
}

void wdunlock(void) {
	if (lfd>=0) {
		close(lfd);
	}
}
//create lockfile(文件锁) in working directory
uint8_t wdlock(uint8_t runmode,uint32_t timeout) {
	pid_t ownerpid;
	pid_t newownerpid;
	uint32_t l;

	//APPNAME的值为mfsmaster
	lfd = open("." STR(APPNAME) ".lock",O_WRONLY|O_CREAT,0666);
	if (lfd<0) {
		mfs_errlog(LOG_ERR,"can't create lockfile in working directory");
		return 1;
	}
	ownerpid = mylock(lfd);
	if (ownerpid<0) {
		mfs_errlog(LOG_ERR,"fcntl error");
		return 1;
	}
	if (ownerpid>0) {
		if (runmode==RM_TEST) {
			fprintf(stderr,STR(APPNAME) " pid: %ld\n",(long)ownerpid);
			return 0;
		}
		if (runmode==RM_START) {
			fprintf(stderr,"can't start: lockfile is already locked by another process\n");
			return 1;
		}
		if (runmode==RM_RELOAD) {
			if (kill(ownerpid,SIGHUP)<0) {
				mfs_errlog(LOG_WARNING,"can't send reload signal to lock owner");
				return 1;
			}
			fprintf(stderr,"reload signal has been sent\n");
			return 0;
		}
		if (runmode==RM_INFO) {
#ifdef SIGINFO
			if (kill(ownerpid,SIGINFO)<0) {
#else
			if (kill(ownerpid,SIGUSR1)<0) {
#endif
				mfs_errlog(LOG_WARNING,"can't send info signal to lock owner");
				return 1;
			}
			fprintf(stderr,"info signal has been sent\n");
			return 0;
		}
		if (runmode==RM_KILL) {
			fprintf(stderr,"sending SIGKILL to lock owner (pid:%ld)\n",(long int)ownerpid);
			if (kill(ownerpid,SIGKILL)<0) {
				mfs_errlog(LOG_WARNING,"can't kill lock owner");
				return 1;
			}
		} else {
			fprintf(stderr,"sending SIGTERM to lock owner (pid:%ld)\n",(long int)ownerpid);
			if (kill(ownerpid,SIGTERM)<0) {
				mfs_errlog(LOG_WARNING,"can't kill lock owner");
				return 1;
			}
		}
		l=0;
		fprintf(stderr,"waiting for termination ");
		fflush(stderr);
		do {
			newownerpid = mylock(lfd);
			if (newownerpid<0) {
				mfs_errlog(LOG_ERR,"fcntl error");
				return 1;
			}
			if (newownerpid>0) {
				l++;
				if (l>=timeout) {
					syslog(LOG_ERR,"about %"PRIu32" seconds passed and lockfile is still locked - giving up",l);
					fprintf(stderr,":giving up\n");
					return 1;
				}
				if (l%10==0) {
					syslog(LOG_WARNING,"about %"PRIu32" seconds passed and lock still exists",l);
					fprintf(stderr,".");
					fflush(stderr);
				}
				if (newownerpid!=ownerpid) {
					fprintf(stderr,"\nnew lock owner detected\n");
					if (runmode==RM_KILL) {
						fprintf(stderr,":sending SIGKILL to lock owner (pid:%ld):",(long int)newownerpid);
						fflush(stderr);
						if (kill(newownerpid,SIGKILL)<0) {
							mfs_errlog(LOG_WARNING,"can't kill lock owner");
							return 1;
						}
					} else {
						fprintf(stderr,":sending SIGTERM to lock owner (pid:%ld):",(long int)newownerpid);
						fflush(stderr);
						if (kill(newownerpid,SIGTERM)<0) {
							mfs_errlog(LOG_WARNING,"can't kill lock owner");
							return 1;
						}
					}
					ownerpid = newownerpid;
				}
			}
			sleep(1);
		} while (newownerpid!=0);
		fprintf(stderr,"terminated\n");
		return 0;
	}
	if (runmode==RM_START || runmode==RM_RESTART) {
		char pidstr[20];
		l = snprintf(pidstr,20,"%ld\n",(long)(getpid()));
		if (ftruncate(lfd,0)<0) {
			fprintf(stderr,"can't truncate pidfile\n");
		}
		if (write(lfd,pidstr,l)!=(ssize_t)l) {
			fprintf(stderr,"can't write pid to pidfile\n");
		}
		fprintf(stderr,"lockfile created and locked\n");
	} else if (runmode==RM_TRY_RESTART) {
		fprintf(stderr,"can't find process to restart\n");
		return 1;
	} else if (runmode==RM_STOP || runmode==RM_KILL) {
		fprintf(stderr,"can't find process to terminate\n");
		return 0;
	} else if (runmode==RM_RELOAD) {
		fprintf(stderr,"can't find process to send reload signal\n");
		return 1;
	} else if (runmode==RM_INFO) {
		fprintf(stderr,"can't find process to send info signal\n");
		return 1;
	} else if (runmode==RM_TEST) {
		fprintf(stderr,STR(APPNAME) " is not running\n");
		return 1;
	}
	return 0;
}

void makedaemon() {
	int f;
	uint8_t pipebuff[1000];
	ssize_t r;
	size_t happy;
	int piped[2];

	fflush(stdout);
	fflush(stderr);
	if (pipe(piped)<0) {
		fprintf(stderr,"pipe error\n");
		exit(1);
	}
	f = fork();
	if (f<0) {
		syslog(LOG_ERR,"first fork error: %s",strerr(errno));
		exit(1);
	}
	if (f>0) {
		wait(&f);	// just get child status - prevents child from being zombie during initialization stage
		if (f) {
			fprintf(stderr,"Child status: %d\n",f);
			exit(1);
		}
		close(piped[1]);
//		printf("Starting daemon ...\n");
		while ((r=read(piped[0],pipebuff,1000))) {
			if (r>0) {
				if (pipebuff[r-1]==0) {	// zero as a last char in the pipe means error
					if (r>1) {
						happy = fwrite(pipebuff,1,r-1,stderr);
						(void)happy;
					}
					exit(1);
				}
				happy = fwrite(pipebuff,1,r,stderr);
				(void)happy;
			} else {
				fprintf(stderr,"Error reading pipe: %s\n",strerr(errno));
				exit(1);
			}
		}
		exit(0);
	}
	setsid();
	setpgid(0,getpid());
	f = fork();
	if (f<0) {
		syslog(LOG_ERR,"second fork error: %s",strerr(errno));
		if (write(piped[1],"fork error\n",11)!=11) {
			syslog(LOG_ERR,"pipe write error: %s",strerr(errno));
		}
		close(piped[1]);
		exit(1);
	}
	if (f>0) {
		exit(0);
	}
	set_signal_handlers(1);

	f = open("/dev/null", O_RDWR, 0);
	close(STDIN_FILENO);
	sassert(dup(f)==STDIN_FILENO);
	close(STDOUT_FILENO);
	sassert(dup(f)==STDOUT_FILENO);
	close(STDERR_FILENO);
	sassert(dup(piped[1])==STDERR_FILENO);
	close(piped[1]);
	close(f); // this stupid construction with open/dup/close is used due to cppcheck false negatives
//	setvbuf(stderr,(char *)NULL,_IOLBF,0);
}

void close_msg_channel() {
	int f;
	//fflush()会强迫将缓冲区内的数据写回参数stream 指定的文件中。
	//stderr【unix】标准输出(设备)文件，对应终端的屏幕。
	fflush(stderr);
	f = open("/dev/null", O_RDWR, 0);
	close(STDERR_FILENO);
	sassert(dup(f)==STDERR_FILENO);
	close(f); // this stupid construction with open/dup/close is used due to cppcheck false negatives
}

void createpath(const char *filename) {
	char pathbuff[1024];
	const char *src = filename;
	char *dst = pathbuff;
	if (*src=='/') *dst++=*src++;

	while (*src) {
		while (*src!='/' && *src) {
			*dst++=*src++;
		}
		if (*src=='/') {
			*dst='\0';
			if (mkdir(pathbuff,(mode_t)0777)<0) {
				if (errno!=EEXIST) {
					mfs_arg_errlog(LOG_NOTICE,"creating directory %s",pathbuff);
				}
			} else {
				mfs_arg_syslog(LOG_NOTICE,"directory %s has been created",pathbuff);
			}
			*dst++=*src++;
		}
	}
}

//输出使用方法
void usage(const char *appname) {
	printf(
"usage: %s [-vfun] [-t locktimeout] [-c cfgfile] " MODULE_OPTIONS_SYNOPIS "[start|stop|restart|reload|info|test|kill|restore]\n"
"\n"
"-v : print version number and exit\n"
"-f : run in foreground\n"
"-u : log undefined config variables\n"
"-n : do not attempt to increase limit of core dump size\n"
"-t locktimeout : how long wait for lockfile\n"
"-c cfgfile : use given config file\n"
MODULE_OPTIONS_DESC
	,appname);
	exit(1);
}

int main(int argc,char **argv) {
	char *logappname;
//	char *lockfname;
	char *wrkdir;
	
	char *cfgfile;		//cfg文件路径
	char *ocfgfile;		//用户设置的cfg文件路径
	char *appname;		//APPNAME的值为mfsmaster
	int ch;
	uint8_t runmode;	//运行模式
	int rundaemon,logundefined;	//rundaemon前后台运行标志，后台为1，前台为0
	int lockmemory;
	int forcecoredump;
	int32_t nicelevel;
	uint32_t locktimeout;
	int fd;

	
	uint8_t movewarning;	//配置文件移动警告标志
	uint8_t userconfig;		//用户设置配置文件标志
	struct rlimit rls;		//资源控制类
#if defined(USE_PTHREADS) && defined(M_ARENA_MAX) && defined(M_ARENA_TEST) && defined(HAVE_MALLOPT)
	uint32_t limit_glibc_arenas;	//配置文件中有类似LIMIT_GLIBC_MALLOC_ARENAS = 4  
									//仅限于Linux：将malloc区域限制为给定值 - 防止服务器使用大量虚拟内存（默认为4）
									//# Linux only: limit malloc arenas to given value - prevents server from using huge amount of virtual memor    y (default is 4)

#endif
 

	strerr_init();					//error hashtab的初始化
	mycrc32_init();					//32位 循环冗余校验码初始化

	movewarning = 0;
	//strdup字符串拷贝库函数 ，需要用free释放空间
	//获取配置文件位置
	cfgfile=strdup(ETC_PATH "/mfs/" STR(APPNAME) ".cfg");
	//passert： cfgflie为空或者指针返回错误，报错并abort
	//判断返回的cfgfile是否有效。
	passert(cfgfile);
	//open函数用来打开或创建一个文件，若成功返回文件描述符，只要有一个权限被禁止则返回-1。O_RDONLY只读打开
	//文件描述符是非负整数。

	//#include <errno.h>
	//errno 把最后一次调用c的方法的错误代码保留。 
	//errno 会返回一个数字，每个数字代表一个错误类型。详细的可以查看头文件。/usr/include/asm/errno.h
	//errno==ENOENT Operation not permitted，操作未被允许
	if ((fd = open(cfgfile,O_RDONLY))<0 && errno==ENOENT) {
		//如果存在权限问题，打开另一个cfg，标记movewarning
		ocfgfile=strdup(ETC_PATH "/" STR(APPNAME) ".cfg");
		passert(ocfgfile);
		if ((fd = open(ocfgfile,O_RDONLY))>=0) {
			free(cfgfile);
			cfgfile = ocfgfile;
			movewarning = 1;
		}
	}
	//成功打开cfgfile
	if (fd>=0) {
		close(fd);
	}
	locktimeout = 1800;
	rundaemon = 1; 			//rundaemon前后台运行标志，后台为1，前台为0
	runmode = RM_START;
	logundefined = 0;
	lockmemory = 0;
	forcecoredump = 1;
	userconfig = 0;
	appname = argv[0];

	//解析传入参数
	//#include<unistd.h>
	//getopt用来分析命令行参数。
	/*
"usage: %s [-vfun] [-t locktimeout] [-c cfgfile] " MODULE_OPTIONS_SYNOPIS "[start|stop|restart|reload|info|test|kill|restore]\n"
"\n"
"-v : print version number and exit\n"
"-f : run in foreground\n"
"-u : log undefined config variables\n"
"-n : do not attempt to increase limit of core dump size\n"
"-t locktimeout : how long wait for lockfile\n"
"-c cfgfile : use given config file\n"
	*/
	while ((ch = getopt(argc, argv, "nuvfdc:t:h?" MODULE_OPTIONS_GETOPT)) != -1) {
		switch(ch) {
			case 'v':
				//输出版本
				printf("version: %s ; build: %s\n",VERSSTR,STR(BUILDNO));
				return 0;
			case 'd':
				printf("option '-d' is deprecated - use '-f' instead\n");
				// no break on purpose
				nobreak;
			case 'f':
				rundaemon=0;	//在前台运行
				break;
			case 't':
				//optarg 指向当前选项参数（如果有）的指针。
				
				//strtoul(optarg,NULL,10);把opt arg转换成10进制的无符号长整数，即把里面的数字提取出来 
				locktimeout=strtoul(optarg,NULL,10);
				break;
			case 'c':
				//按照用户的配置cfg
				free(cfgfile);
				cfgfile = strdup(optarg);
				passert(cfgfile);
				movewarning = 0;
				userconfig = 1;
				break;
			case 'u':
				logundefined=1;
				break;
			case 'n':
				forcecoredump = 0;
				break;
			MODULE_OPTIONS_SWITCH
			default:
				usage(appname);
				return 1;
		}
	}
	//optind 再次调用 getopt() 时的下一个 argv 指针的索引。
	argc -= optind;
	argv += optind;
	//获取运行模式
	if (argc==1) {
		//strcasecmp用忽略大小写比较字符串。
		//若参数s1和s2字符串相等则返回0。s1大于s2则返回大于0 的值，s1 小于s2 则返回小于0的值。
		if (strcasecmp(argv[0],"start")==0) {
			runmode = RM_START;
		} else if (strcasecmp(argv[0],"stop")==0) {
			runmode = RM_STOP;
		} else if (strcasecmp(argv[0],"restart")==0) {
			runmode = RM_RESTART;
		} else if (strcasecmp(argv[0],"try-restart")==0) {
			runmode = RM_TRY_RESTART;
		} else if (strcasecmp(argv[0],"reload")==0) {
			runmode = RM_RELOAD;
		} else if (strcasecmp(argv[0],"info")==0) {
			runmode = RM_INFO;
		} else if (strcasecmp(argv[0],"test")==0 || strcasecmp(argv[0],"status")==0) {
			runmode = RM_TEST;
		} else if (strcasecmp(argv[0],"kill")==0) {
			runmode = RM_KILL;
		} else if (strcasecmp(argv[0],"restore")==0) {
			runmode = RM_RESTORE;
		} else {
			usage(appname);
			return 1;
		}
	} else if (argc!=0) {
		usage(appname);
		return 1;
	}

	//如果之前配置文件打开权限有问题，提醒配置文件路径变了，需要移动到默认位置
	if (movewarning) {
		mfs_syslog(LOG_WARNING,"default sysconf path has changed - please move " STR(APPNAME) ".cfg from "ETC_PATH"/ to "ETC_PATH"/mfs/");
	}
	//Daemon程序,又称为守护进程
	if (runmode==RM_START || runmode==RM_RESTART || runmode==RM_TRY_RESTART) {
		if (rundaemon) {
			////在后台运行则运行守护进程
			makedaemon();
		} else {
			//设置信号处理器
			set_signal_handlers(0);
		}
	}

	//加载配置文件，填充paramhead参数链表
	if (cfg_load(cfgfile,logundefined)==0) {
		//如果用户设置了配置文件
		if (userconfig) {
			//且在后台运行
			if (rundaemon) {
				//stderr标准错误输出设备
				//int fputc (int c, FILE *fp)功能是将字符c写到文件指针fp所指向的文件的当du前写指针的位置
				fputc(0,stderr);
				//关闭信息通道
				close_msg_channel();
			}
			return 1;
		}
		fprintf(stderr,"can't load config file: %s - using defaults\n",cfgfile);
	}
	//free释放资源
	free(cfgfile);

	//processname_init 其中processname分为四类：mfsmaster、mfscgiserv、mfsmetalogger、mfschunkserver
	processname_init(argc_back,argv_back); // prepare everything for 'processname_set'

	logappname = cfg_getstr("SYSLOG_IDENT",STR(APPNAME));

	if (rundaemon) {
		if (logappname[0]) {
			//openlog()打开一个程序的系统记录器的连接。#include<syslog.h>
			openlog(logappname, LOG_PID | LOG_NDELAY , LOG_DAEMON);
		} else {
			openlog(STR(APPNAME), LOG_PID | LOG_NDELAY , LOG_DAEMON);
		}
	} else {
	//LOG_PERROR = log process error？？？
#if defined(LOG_PERROR)
		if (logappname[0]) {
			openlog(logappname, LOG_PID | LOG_NDELAY | LOG_PERROR, LOG_USER);
		} else {
			openlog(STR(APPNAME), LOG_PID | LOG_NDELAY | LOG_PERROR, LOG_USER);
		}
#else
		if (logappname[0]) {
			openlog(logappname, LOG_PID | LOG_NDELAY, LOG_USER);
		} else {
			openlog(STR(APPNAME), LOG_PID | LOG_NDELAY, LOG_USER);
		}
#endif
	}
	//如果runmode是RM_START、RM_RESTART、RM_TRY_RESTART，判断set files limit是否成功
	if (runmode==RM_START || runmode==RM_RESTART || runmode==RM_TRY_RESTART) {
		rls.rlim_cur = MFSMAXFILES;
		rls.rlim_max = MFSMAXFILES;
		//setrlimit设置资源使用限制
		//成功执行时，返回0。失败返回-1，errno被设为以下的某个值 
		//	EFAULT：rlim指针指向的空间不可访问 
		//	EINVAL：参数无效 
		//	EPERM：增加资源限制值时，权能不允许
		if (setrlimit(RLIMIT_NOFILE,&rls)<0) {
			syslog(LOG_NOTICE,"can't change open files limit to: %u (trying to set smaller value)",(unsigned)(MFSMAXFILES));
			//getrlimit获取资源使用限制。
			//判断资源使用限制各种情况
			if (getrlimit(RLIMIT_NOFILE,&rls)>=0) {
				uint32_t limit;
				if (rls.rlim_max > MFSMAXFILES) {
					limit = MFSMAXFILES;
				} else {
					limit = rls.rlim_max;
				}
				while (limit>1024) {
					rls.rlim_cur = limit;
					if (setrlimit(RLIMIT_NOFILE,&rls)>=0) {
						mfs_arg_syslog(LOG_NOTICE,"open files limit has been set to: %"PRIu32,limit);
						break;
					}
					limit *= 3;
					limit /= 4;
				}
			}
		} else {
			mfs_arg_syslog(LOG_NOTICE,"open files limit has been set to: %u",(unsigned)(MFSMAXFILES));
		}

		lockmemory = cfg_getnum("LOCK_MEMORY",0);
#ifdef MFS_USE_MEMLOCK
		if (lockmemory) {
			rls.rlim_cur = RLIM_INFINITY;
			rls.rlim_max = RLIM_INFINITY;
			setrlimit(RLIMIT_MEMLOCK,&rls);
		}
#endif
		nicelevel = cfg_getint32("NICE_LEVEL",-19);
		setpriority(PRIO_PROCESS,getpid(),nicelevel);
	}
	//改变用户uid，修改获取权限
	changeugid(); 

	//获取DATA_PATH
	wrkdir = cfg_getstr("DATA_PATH",DATA_PATH);
	if (runmode==RM_START || runmode==RM_RESTART || runmode==RM_TRY_RESTART) {
		fprintf(stderr,"working directory: %s\n",wrkdir);
	}

	//chdir更改当前工作目录。成功返回0 ，失败返回-1
	if (chdir(wrkdir)<0) {
		mfs_arg_syslog(LOG_ERR,"can't set working directory to %s",wrkdir);
		if (rundaemon) {
			fputc(0,stderr);
			close_msg_channel();
		}
		closelog();
		free(logappname);
		return 1;
	}
	free(wrkdir);

	umask(cfg_getuint32("FILE_UMASK",027)&077);

	//工作目录创建文件锁
	ch = wdlock(runmode,locktimeout);
	//如果失败，释放资源
	if (ch) {
		if (rundaemon) {
			fputc(0,stderr);
			close_msg_channel();
		}
		signal_cleanup();
		cfg_term();
		strerr_term();
		wdunlock();
		closelog();
		free(logappname);
		return ch;
	}

	ch = 0; // practically not needed after above condition - left for code elegance
	if (runmode==RM_RESTORE) {
		if (restore()==0) {
			ch = 1;
		}
	}

	//如果runmode为RM_STOP、RM_KILL、RM_RELOAD、RM_INFO、RM_TEST、RM_RESTORE，释放资源
	if (runmode==RM_STOP || runmode==RM_KILL || runmode==RM_RELOAD || runmode==RM_INFO || runmode==RM_TEST || runmode==RM_RESTORE) {
		if (rundaemon) {
			close_msg_channel();
		}
		//释放资源
		signal_cleanup();
		cfg_term();
		strerr_term();
		wdunlock();
		closelog();
		free(logappname);
		return ch;
	}

#ifdef MFS_USE_MEMLOCK
	if (lockmemory) {
		if (getrlimit(RLIMIT_MEMLOCK,&rls)<0) {
			mfs_errlog(LOG_WARNING,"error getting memory lock limits");
		} else {
			if (rls.rlim_cur!=RLIM_INFINITY && rls.rlim_max==RLIM_INFINITY) {
				rls.rlim_cur = RLIM_INFINITY;
				rls.rlim_max = RLIM_INFINITY;
				if (setrlimit(RLIMIT_MEMLOCK,&rls)<0) {
					mfs_errlog(LOG_WARNING,"error setting memory lock limit to unlimited");
				}
			}
			if (getrlimit(RLIMIT_MEMLOCK,&rls)<0) {
				mfs_errlog(LOG_WARNING,"error getting memory lock limits");
			} else {
				if (rls.rlim_cur!=RLIM_INFINITY) {
					mfs_errlog(LOG_WARNING,"can't set memory lock limit to unlimited");
				} else {
					if (mlockall(MCL_CURRENT|MCL_FUTURE)<0) {
						mfs_errlog(LOG_WARNING,"memory lock error");
					} else {
						mfs_syslog(LOG_NOTICE,"process memory was successfully locked in RAM");
					}
			}	}
		}
	}
#else
	if (lockmemory) {
		mfs_syslog(LOG_WARNING,"memory lock not supported !!!");
	}
#endif

	if (forcecoredump) {
		rls.rlim_cur = RLIM_INFINITY;
		rls.rlim_max = RLIM_INFINITY;
		setrlimit(RLIMIT_CORE,&rls);
#if defined(HAVE_PRCTL) && defined(PR_SET_DUMPABLE)
		prctl(PR_SET_DUMPABLE,1);
#endif
	}


/* glibc malloc tuning */
//防止服务器使用大量虚拟内存
#if defined(USE_PTHREADS) && defined(M_ARENA_MAX) && defined(M_ARENA_TEST) && defined(HAVE_MALLOPT)
	limit_glibc_arenas = cfg_getuint8("LIMIT_GLIBC_MALLOC_ARENAS",4);
	if (limit_glibc_arenas) {
		if (!getenv("MALLOC_ARENA_MAX")) {
			mfs_arg_syslog(LOG_NOTICE,"setting glibc malloc arena max to %"PRIu32,limit_glibc_arenas);
			mallopt(M_ARENA_MAX, limit_glibc_arenas);
		}
		if (!getenv("MALLOC_ARENA_TEST")) {
			mfs_arg_syslog(LOG_NOTICE,"setting glibc malloc arena test to %"PRIu32,limit_glibc_arenas);
			mallopt(M_ARENA_TEST, limit_glibc_arenas);
		}
	} else {
		mfs_syslog(LOG_NOTICE,"setting glibc malloc arenas turned off");
	}
#endif /* glibc malloc tuning */


//OMM out of memory 关闭OMM
//现代Linux内核中都会有一个内存不足终结者（Out of memory Killer, OOM Killer）的内建机制，在内存过低的情况下，它会杀掉你的进程。
#if defined(__linux__) && defined(OOM_ADJUSTABLE)
	if (cfg_getuint8("DISABLE_OOM_KILLER",1)==1) {
		FILE *oomfd;
		int oomdis;
		oomdis = 0;
#  if defined(OOM_SCORE_ADJ_MIN)
		oomfd = fopen("/proc/self/oom_score_adj","w");
		if (oomfd!=NULL) {
			fprintf(oomfd,"%d\n",OOM_SCORE_ADJ_MIN);
			fclose(oomfd);
			oomdis = 1;
#    if defined(OOM_DISABLE)
		} else {
			oomfd = fopen("/proc/self/oom_adj","w");
			if (oomfd!=NULL) {
				fprintf(oomfd,"%d\n",OOM_DISABLE);
				fclose(oomfd);
				oomdis = 1;
			}
#    endif
		}
#  elif defined(OOM_DISABLE)
		oomfd = fopen("/proc/self/oom_adj","w");
		if (oomfd!=NULL) {
			fprintf(oomfd,"%d\n",OOM_DISABLE);
			fclose(oomfd);
			oomdis = 1;
		}
#  endif
		if (oomdis) {
			syslog(LOG_NOTICE,"out of memory killer disabled");
		} else {
			syslog(LOG_NOTICE,"can't disable out of memory killer");
		}
	}
#endif

	syslog(LOG_NOTICE,"monotonic clock function: %s",monotonic_method());
	syslog(LOG_NOTICE,"monotonic clock speed: %"PRIu32" ops / 10 mili seconds",monotonic_speed());

	fprintf(stderr,"initializing %s modules ...\n",logappname);

	//如果初始化成功
	if (initialize()) {
//		if (getrlimit(RLIMIT_NOFILE,&rls)==0) {
//			syslog(LOG_NOTICE,"open files limit: %lu",(unsigned long)(rls.rlim_cur));
//		}
		//初始化成功
		fprintf(stderr,"%s daemon initialized properly\n",logappname);
		if (rundaemon) {
			//关闭消息通道
			close_msg_channel();
		}
		//mainloop循环
		if (initialize_late()) {
			mainloop();
			mfs_syslog(LOG_NOTICE,"exited from main loop");
			ch=0;
		} else {
			ch=1;
		}
	} else {
		//初始化失败
		fprintf(stderr,"error occurred during initialization - exiting\n");
		if (rundaemon) {
			//fputc (int c, FILE *fp): 将字符ch写到文件指针fp所指向的文件的当前写指针的位置。
			fputc(0,stderr);
			close_msg_channel();
		}
		ch=1;
	}
	mfs_syslog(LOG_NOTICE,"exititng ...");

	//释放资源
	destruct();
	free_all_registered_entries();
	signal_cleanup();
	cfg_term();
	strerr_term();
	wdunlock();
	mfs_arg_syslog(LOG_NOTICE,"process exited successfully (status:%d)",ch);
	closelog();
	free(logappname);
	return ch;
}
