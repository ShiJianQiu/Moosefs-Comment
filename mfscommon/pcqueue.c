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
#include <pthread.h>
#include <inttypes.h>
#include <errno.h>

#include "massert.h"

typedef struct _qentry {
	uint32_t id;//队列元素id，实际就是job.jobid
	uint32_t op;//块操作类型
	uint8_t *data;//队列元素实体，实际该指针指向一个job
	uint32_t leng;//队列元素的长度，一般是1表示一个job
	struct _qentry *next;//指向下一个队列元素
} qentry;//队列元素

typedef struct _queue {
	qentry *head,**tail;//队列的头尾指针
	uint32_t elements;//队列中qentry总个数
	uint32_t size;//队列长度，即所有qentry.leng的和，一般可以认为是该队列中job的总数

	uint32_t maxsize;//队列允许的最大长度，默认为1000
	uint32_t freewaiting;//在queue_get函数中，当elements为0时，即当前队列是空的，该值会++，
						//同时线程（块操作处理线程job_worker）会阻塞到q->waitfree这个条件变量，
						//以等待其他线程将其唤醒
	uint32_t fullwaiting;//在queue_put函数中，当队列size大于maxsize，该值会++，
						//同时线程（事实上是mfschunkserver主线程）会阻塞到q->waitfull这个条件变量，
						//以等待其他线程将其唤醒
	uint32_t closed;
	pthread_cond_t waitfree,waitfull;
	pthread_mutex_t lock;//队列的互斥锁
} queue;//队列

void* queue_new(uint32_t size) {
	queue *q;
	q = (queue*)malloc(sizeof(queue));
	passert(q);
	q->head = NULL;
	q->tail = &(q->head);
	q->elements = 0;
	q->size = 0;
	q->maxsize = size;
	q->freewaiting = 0;
	q->fullwaiting = 0;
	q->closed = 0;
	if (size) {
		zassert(pthread_cond_init(&(q->waitfull),NULL));
	}
	zassert(pthread_cond_init(&(q->waitfree),NULL));
	zassert(pthread_mutex_init(&(q->lock),NULL));
	return q;
}

void queue_delete(void *que) {
	queue *q = (queue*)que;
	qentry *qe,*qen;
	zassert(pthread_mutex_lock(&(q->lock)));
	sassert(q->freewaiting==0);
	sassert(q->fullwaiting==0);
	for (qe = q->head ; qe ; qe = qen) {
		qen = qe->next;
		free(qe->data);
		free(qe);
	}
	zassert(pthread_mutex_unlock(&(q->lock)));
	zassert(pthread_mutex_destroy(&(q->lock)));
	zassert(pthread_cond_destroy(&(q->waitfree)));
	if (q->maxsize) {
		zassert(pthread_cond_destroy(&(q->waitfull)));
	}
	free(q);
}

void queue_close(void *que) {
	queue *q = (queue*)que;
	zassert(pthread_mutex_lock(&(q->lock)));
	q->closed = 1;
	if (q->freewaiting>0) {
		zassert(pthread_cond_broadcast(&(q->waitfree)));
		q->freewaiting = 0;
	}
	if (q->fullwaiting>0) {
		zassert(pthread_cond_broadcast(&(q->waitfull)));
		q->fullwaiting = 0;
	}
	zassert(pthread_mutex_unlock(&(q->lock)));
}

int queue_isempty(void *que) {
	queue *q = (queue*)que;
	int r;
	zassert(pthread_mutex_lock(&(q->lock)));
	r=(q->elements==0)?1:0;
	zassert(pthread_mutex_unlock(&(q->lock)));
	return r;
}

uint32_t queue_elements(void *que) {
	queue *q = (queue*)que;
	uint32_t r;
	zassert(pthread_mutex_lock(&(q->lock)));
	r=q->elements;
	zassert(pthread_mutex_unlock(&(q->lock)));
	return r;
}

int queue_isfull(void *que) {
	queue *q = (queue*)que;
	int r;
	zassert(pthread_mutex_lock(&(q->lock)));
	r = (q->maxsize>0 && q->maxsize<=q->size)?1:0;
	zassert(pthread_mutex_unlock(&(q->lock)));
	return r;
}

uint32_t queue_sizeleft(void *que) {
	queue *q = (queue*)que;
	uint32_t r;
	zassert(pthread_mutex_lock(&(q->lock)));
	if (q->maxsize>0) {
		r = q->maxsize-q->size;
	} else {
		r = 0xFFFFFFFF;
	}
	zassert(pthread_mutex_unlock(&(q->lock)));
	return r;
}

int queue_put(void *que,uint32_t id,uint32_t op,uint8_t *data,uint32_t leng) {
	queue *q = (queue*)que;
	//初始化队列元素
	qentry *qe;
	qe = malloc(sizeof(qentry));
	passert(qe);
	qe->id = id;
	qe->op = op;
	qe->data = data;
	qe->leng = leng;
	qe->next = NULL;
	zassert(pthread_mutex_lock(&(q->lock)));
	if (q->maxsize) {
		if (leng>q->maxsize) {
			zassert(pthread_mutex_unlock(&(q->lock)));
			free(qe);
			errno = EDEADLK;
			return -1;
		}
		while (q->size+leng>q->maxsize && q->closed==0) {
			q->fullwaiting++;
			zassert(pthread_cond_wait(&(q->waitfull),&(q->lock)));
		}
		if (q->closed) {
			zassert(pthread_mutex_unlock(&(q->lock)));
			free(qe);
			errno = EIO;
			return -1;
		}
	}
	q->elements++;
	q->size += leng;
	*(q->tail) = qe;
	q->tail = &(qe->next);
	if (q->freewaiting>0) {
		zassert(pthread_cond_signal(&(q->waitfree)));
		q->freewaiting--;
	}
	zassert(pthread_mutex_unlock(&(q->lock)));
	return 0;
}

int queue_tryput(void *que,uint32_t id,uint32_t op,uint8_t *data,uint32_t leng) {
	queue *q = (queue*)que;
	qentry *qe;
	zassert(pthread_mutex_lock(&(q->lock)));
	if (q->maxsize) {
		if (leng>q->maxsize) {
			zassert(pthread_mutex_unlock(&(q->lock)));
			errno = EDEADLK;
			return -1;
		}
		if (q->size+leng>q->maxsize) {
			zassert(pthread_mutex_unlock(&(q->lock)));
			errno = EBUSY;
			return -1;
		}
	}
	qe = malloc(sizeof(qentry));
	passert(qe);
	qe->id = id;
	qe->op = op;
	qe->data = data;
	qe->leng = leng;
	qe->next = NULL;
	q->elements++;
	q->size += leng;
	*(q->tail) = qe;
	q->tail = &(qe->next);
	if (q->freewaiting>0) {
		zassert(pthread_cond_signal(&(q->waitfree)));
		q->freewaiting--;
	}
	zassert(pthread_mutex_unlock(&(q->lock)));
	return 0;
}

//获取que里第一个任务qe，并把qe对象的内容传递给其他形参，其中data里存放的是job指针
////函数用于从队列中取出一个队列元素，当队列为空时当前线程阻塞。
int queue_get(void *que,uint32_t *id,uint32_t *op,uint8_t **data,uint32_t *leng) {
	queue *q = (queue*)que;
	qentry *qe;
	zassert(pthread_mutex_lock(&(q->lock)));
	while (q->elements==0 && q->closed==0) {
		q->freewaiting++;
		zassert(pthread_cond_wait(&(q->waitfree),&(q->lock)));
	}
	if (q->closed) {
		zassert(pthread_mutex_unlock(&(q->lock)));
		if (id) {
			*id=0;
		}
		if (op) {
			*op=0;
		}
		if (data) {
			*data=NULL;
		}
		if (leng) {
			*leng=0;
		}
		errno = EIO;
		return -1;
	}
	//获取队列首元素
	qe = q->head;
	q->head = qe->next;
	if (q->head==NULL) {
		q->tail = &(q->head);
	}
	q->elements--;
	q->size -= qe->leng;
	if (q->fullwaiting>0) {
		zassert(pthread_cond_signal(&(q->waitfull)));
		q->fullwaiting--;
	}
	zassert(pthread_mutex_unlock(&(q->lock)));
	if (id) {
		*id = qe->id;
	}
	if (op) {
		*op = qe->op;
	}
	if (data) {
		*data = qe->data;
	}
	if (leng) {
		*leng = qe->leng;
	}
	free(qe);
	return 0;
}
//函数用于从队列中取出一个队列元素，当队列为空时当前线程不阻塞。
int queue_tryget(void *que,uint32_t *id,uint32_t *op,uint8_t **data,uint32_t *leng) {
	queue *q = (queue*)que;
	qentry *qe;
	zassert(pthread_mutex_lock(&(q->lock)));
	if (q->elements==0) {
		zassert(pthread_mutex_unlock(&(q->lock)));
		if (id) {
			*id=0;
		}
		if (op) {
			*op=0;
		}
		if (data) {
			*data=NULL;
		}
		if (leng) {
			*leng=0;
		}
		errno = EBUSY;
		return -1;
	}
	qe = q->head;
	q->head = qe->next;
	if (q->head==NULL) {
		q->tail = &(q->head);
	}
	q->elements--;
	q->size -= qe->leng;
	if (q->fullwaiting>0) {
		zassert(pthread_cond_signal(&(q->waitfull)));
		q->fullwaiting--;
	}
	zassert(pthread_mutex_unlock(&(q->lock)));
	if (id) {
		*id = qe->id;
	}
	if (op) {
		*op = qe->op;
	}
	if (data) {
		*data = qe->data;
	}
	if (leng) {
		*leng = qe->leng;
	}
	free(qe);
	return 0;
}
