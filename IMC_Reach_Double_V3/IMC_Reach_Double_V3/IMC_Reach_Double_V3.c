//
//  main.c
//  IMC_Reach_Double_V3
//
//  Created by 孙知兵 on 2023/8/4.
//

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <math.h>

#define CLR_BIT(x,n) ( (x) &= ~(1 << (n)) )
#define SET_BIT(x,n) ( (x) |= (1 << (n)) )
#define GET_BIT(x,n) ( ((x)>>(n)) & 1 )

//#define DBL_EPSILON 2.2204460492503131e-16
const double MACHINE_EPSILON=__DBL_EPSILON__/2;
const double EPS=2*MACHINE_EPSILON;
const double REL_ERR_THRES = 1.0;
const double EPSILON=1*MACHINE_EPSILON; // user-defined tolerance
const double EPSILON1=64*MACHINE_EPSILON; // user-defined tolerance
const double EPSILON2=0*MACHINE_EPSILON; // user-defined tolerance

#define ITERATION_BOUND 10

#define ITERATION_BOUND1 10

#define ITERATION_BOUND2 10

#define MULTIPLIER 1000


typedef struct OUT_EDGE{uint32_t x2;uint16_t next,num;double p_l,p_u,p;}OUT_EDGE;

typedef struct IN_EDGE{uint32_t x1;uint16_t pos;}IN_EDGE;

typedef uint8_t BOOL;

uint32_t *permutation;

typedef struct IMC
{
    OUT_EDGE **out_pos,**out_pos_reset,*out_edge,**sort_edge;
    uint16_t *in_deg;
    IN_EDGE **in_pos,*in_edge;
    double *x_vec,*b_vec,**sort_x;
    uint32_t n;
    uint64_t m;
    uint32_t *queue,l0,l1,l2,l3;
}IMC;

typedef struct HEAD
{
    uint16_t imc_num,label_num;
    uint32_t *encode_max,*decode_max,*encode_min,*decode_min;
    IMC imc;
    uint32_t l2_max,l2_min;
    double *x_vec_power_max,*x_vec_Jacobi_max,*x_vec_Gauss_Seidel_max;
    double *x_vec_power_min,*x_vec_Jacobi_min,*x_vec_Gauss_Seidel_min;
    BOOL *flag_max,*flag_min;
}HEAD;

// Kahan's compansated summation algorithm
/*
 s=0; e=0;
 for i=1:n
    tmp = s;
    y = x_i + e;
    s = tmp + y;
    e = (tmp - s) + y;
 end
 */

/*
    sum and x_i are both non-negative, sum+=x_i.
 */
void sum_p(double *p_sum,double *p_err,double x_i)
{
    double tmp,y;
    if(*p_sum>=x_i)
    {
        tmp=*p_sum;
        y=x_i+*p_err;
        *p_sum=tmp+y;
        *p_err=(tmp-*p_sum)+y;
    }
    else
    {
        tmp=*p_sum+x_i;
        *p_err+=(x_i-tmp)+*p_sum;
        *p_sum=tmp;
    }
}
/*
 sum and x_i are both non-negative, sum>=x_i, sum-=x_i.
 */
void sum_m(double *p_sum,double *p_err,double x_i)
{
    if(*p_sum<=2*x_i){*p_sum-=x_i;return;}
    double tmp,y;
    tmp=*p_sum;
    y=-x_i+*p_err;
    *p_sum=tmp+y;
    *p_err=(tmp-*p_sum)+y;
}

//ascending order
int cmp1(const void *a,const void *b)
{
    double x=**(double**)a-**(double**)b;
    if(x==0.0)return *(double**)a<*(double**)b?-1:1;
    return x<0.0?-1:1;
}

// ascending order
int cmp2(const void *a,const void *b)
{
    return *(permutation+(*(OUT_EDGE**)a)->x2)<*(permutation+(*(OUT_EDGE**)b)->x2)?-1:1;
}

void initialization(HEAD *head)
{
    IMC *imc;
    clock_t start_t,end_t;
    
    imc=&head->imc;
    
    // MARK: initialize variables to 0
    start_t=clock();
    printf("Initialize variables to 0:\n");
    
    permutation=0;
    
    // initialize HEAD
    head->encode_max=head->decode_max=0;
    head->encode_min=head->decode_min=0;
    head->l2_max=head->l2_min=0;
    head->x_vec_power_max=head->x_vec_Jacobi_max=head->x_vec_Gauss_Seidel_max=0;
    head->x_vec_power_min=head->x_vec_Jacobi_min=head->x_vec_Gauss_Seidel_min=0;
    head->flag_max=head->flag_min=0;
    
    // initialize IMC
    imc->out_pos=imc->out_pos_reset=imc->sort_edge=0;imc->out_edge=0;imc->in_deg=0;
    imc->in_pos=0;imc->in_edge=0;
    imc->x_vec=imc->b_vec=0;imc->sort_x=0;imc->queue=0;imc->n=0;
    end_t=clock();
    printf("Time used to initialize variables to 0 = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void input_imc_post(HEAD *head)
{
    IMC *imc;
    uint64_t n0,m0;
    OUT_EDGE **p1,**p2,**p4,*p3,*p5;
    uint16_t *in_deg;
    uint32_t x2,cnt_p_l,cnt_p_u,cnt_gap_min,cnt_gap_max;
    double err1,err2,p_l_min,p_u_max,sum_l_min,sum_u_max,gap_min,gap_max;
    char buffer[40];
    FILE *fin;
    clock_t start_t0,start_t,end_t;
    
    imc=&head->imc;
    
    // MARK: input imc in posts
    start_t0=start_t=clock();
    printf("Input imc in posts:\n");
    /*
     "imcX.txt" gives the info of an interval Markov chain in its posts,
     with a format:
     1-st line: n0 m0
     where n0 is the # of states, of type uint32_t,
     the indexes are from 0 to n0-1;
     m0 is the # of transitions, of type uint64_t;
     from 2-nd line to n0+1-th line: each line represents the outgoing edges of the corresponding node from 0 to n0-1, the edges on each line are sorted in ascending order w.r.t. x2(it's not necessary to have order, but would be more efficient if we do),
     each edge has the format x2 p_l p_u, which represents an outgoing edge from the current state to state x2, with lower and upper transition probabilities p_l and p_u respectively; each line ends with n0.
     */
    sprintf(buffer,"imc%hu.txt",head->imc_num);
    printf("Read imc from %s:\n",buffer);
    fin=fopen(buffer,"rb");
    fscanf(fin,"%llu%llu",&n0,&m0);
    if(n0>=UINT32_MAX)
    {
        printf("n0 >= UINT32_MAX, change uint32_t to uint64_t.\n");
        return;
    }
    imc->n=(uint32_t)n0;imc->m=m0;
    printf("# of states n0: %llu\n",n0);
    printf("# of transitions m0: %llu\n",m0);
    printf("Average degree of mc m0/n0 = %llu\n",m0/n0);
    
    p1=imc->out_pos=(OUT_EDGE**)malloc(n0*sizeof(OUT_EDGE*));
    // out_pos_reset
    p4=imc->out_pos_reset=(OUT_EDGE**)malloc((n0+1)*sizeof(OUT_EDGE*));
    
    p3=imc->out_edge=(OUT_EDGE*)malloc((m0+n0)*sizeof(OUT_EDGE));
    imc->in_deg=in_deg=(uint16_t*)calloc(n0,sizeof(uint16_t));
    
    p_l_min=1.0;p_u_max=0.0;sum_l_min=1.0;sum_u_max=1.0;gap_min=1.0;gap_max=0.0;
    cnt_p_l=cnt_p_u=cnt_gap_min=cnt_gap_max=0;
    
    for(p2=p1+n0;p1!=p2;++p1,++p4)
    {
        
        p5=p3;p5->p_l=p5->p_u=err1=err2=0.0;
        
        for(*p4=*p1=p3;fscanf(fin,"%u",&x2)&&x2!=n0;)
        {
            p3++->next=1;p3->x2=x2;
            fscanf(fin,"%lf%lf",&p3->p_l,&p3->p_u);
            ++*(in_deg+x2);
            
            if(p3->p_l>p3->p_u)printf("error: p_l > p_u\n");
            
            if(p3->p_l<p_l_min&&p3->p_l!=0.0)p_l_min=p3->p_l;
            if(p3->p_l==0.0)++cnt_p_l;
            
            if(p3->p_u>p_u_max&&p3->p_u!=1.0)p_u_max=p3->p_u;
            if(p3->p_u==1.0)
            {++cnt_p_u;
                printf("p_u(%u,%u) == 1.0\n",(uint32_t)(p1-imc->out_pos),p3->x2);
            }
            
            if(p3->p_u-p3->p_l<gap_min&&p3->p_u!=p3->p_l)gap_min=p3->p_u-p3->p_l;
            if(p3->p_u==p3->p_l)
            {
                ++cnt_gap_min;
                printf("p(%u,%u): p_u=p_l=%.17e\n",(uint32_t)(p1-imc->out_pos),p3->x2,p3->p_u);
            }
            
            if(p3->p_u-p3->p_l>gap_max)gap_max=p3->p_u-p3->p_l;
            if(p3->p_u-p3->p_l==1.0)
            {
                ++cnt_gap_max;
                printf("p(%u,%u): p_u-p_l=1.0, p_u = %.17e\n",(uint32_t)(p1-imc->out_pos),p3->x2,p3->p_u);
            }
            
            sum_p(&p5->p_l,&err1,p3->p_l);
            sum_p(&p5->p_u,&err2,p3->p_u);
//            p5->p_l+=p3->p_l;
//            p5->p_u+=p3->p_u;
        }
        p3++->next=0;
        
        if(p5->p_l>1.0)printf("error: sum_l > 1\n");
        if(p5->p_u<1.0)printf("error: sum_u < 1\n");
        if(p5->p_l<sum_l_min)sum_l_min=p5->p_l;
        if(p5->p_u>sum_u_max)sum_u_max=p5->p_u;
    }
    *p4=p3;
    fclose(fin);
    printf("Non-zero p_l_min = %.17e, # p_l == 0.0 = %u\n",p_l_min,cnt_p_l);
    printf("Non-one p_u_max = %.17e, # p_u == 1.0 = %u\n",p_u_max,cnt_p_u);
    printf("Non-zero gap_min = %.17e, # gap_min == 0.0 = %u\n",gap_min,cnt_gap_min);
    printf("gap_max = %.17e, # gap_max == 1.0 = %u\n",gap_max,cnt_gap_max);
    printf("sum_l_min = %.17e, 1.0-sum_l_min = %.17e\n",sum_l_min,1.0-sum_l_min);
    printf("sum_u_max = %.17e, sum_u_max-1.0 = %.17e\n",sum_u_max,sum_u_max-1.0);
    
    end_t=clock();
    printf("Time used to input imc_post = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void input_label_and_post2pre(HEAD *head)
{
    IMC *imc;
    uint32_t n0,cnt1;
    uint64_t cnt2;
    OUT_EDGE **out_pos,**p1,*p3;
    uint16_t *in_deg,*p9,*p10;
    IN_EDGE **in_pos,*in_edge,*p4,**p5;
    uint32_t x1;
    BOOL *flag_max,*flag_min;
    char buffer[40];
    FILE *fin;
    clock_t start_t0,start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    out_pos=imc->out_pos;
    in_deg=imc->in_deg;
    n0=imc->n;
    
    printf("Input label and convert transitions from post to pre:\n");
    
    // MARK: input label
    start_t0=start_t=clock();
    printf("Input label and set target:\n");
    /*
     "labelX_X.txt" gives the info of the label of imc,
     with a format:
     each line represents the states with that label, ends with n0;
     the indexes of the states are from 0 to n0-1,
     these states are of type uint32_t.
     */
    sprintf(buffer,"label%hu_%hu.txt",head->imc_num,head->label_num);
    printf("Read label from %s:\n",buffer);
    fin=fopen(buffer,"rb");
    head->flag_max=flag_max=(BOOL*)calloc(n0,sizeof(BOOL));
    head->flag_min=flag_min=(BOOL*)calloc(n0,sizeof(BOOL));
    for(cnt1=0;fscanf(fin,"%u",&x1)&&x1!=n0;)
    {
        *(flag_max+x1)=1;*(flag_min+x1)=1;++cnt1;
        for(p3=*(out_pos+x1);p3->next;)
        {p3+=p3->next;--*(in_deg+p3->x2);}
        *(out_pos+x1)=0;
    }
    imc->l1=cnt1;
    fclose(fin);
    end_t=clock();
    printf("Time used to input label and set target = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    
    // MARK: post2pre
    // If imc_post is in ascending order, then imc_pre is in ascending order.
    start_t=clock();
    printf("Convert transitions from post to pre:\n");
    for(p9=in_deg,p10=p9+n0,cnt1=cnt2=0;p9!=p10;++p9)
        if(*p9){++cnt1;cnt2+=*p9;}
    p5=imc->in_pos=in_pos=(IN_EDGE**)malloc(n0*sizeof(IN_EDGE*));
    p4=imc->in_edge=in_edge=(IN_EDGE*)malloc((cnt1+cnt2)*sizeof(IN_EDGE));
    for(p9=in_deg;p9!=p10;++p9,++p5)
        if(*p9){*p5=p4;p4+=*p9;p4++->x1=n0;*p9=0;}
        else *p5=0;
    for(cnt1=0,p1=out_pos;cnt1!=n0;++p1,++cnt1)
        if(*p1)// not target
        {
            for(p3=*p1;p3->next;)
            {
                p3+=p3->next;
                p9=in_deg+p3->x2;
                p4=*(in_pos+p3->x2)+(*p9)++;
                p4->x1=cnt1;
                p4->pos=p3-*p1;
            }
        }
    free(in_deg);imc->in_deg=0;
    end_t=clock();
    printf("Time used to convert transitions from post to pre = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("Total time used to input label and convert transitions from post to pre: = %.4f\n",
           (double)(end_t-start_t0)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void solve_qualitative_max_reachability(HEAD *head)
{
    IMC *imc;
    uint32_t n0,cnt1;
    OUT_EDGE **out_pos,*p2,*p3;
    IN_EDGE **in_pos,*p4;
    uint32_t *queue,*p7,*p8,*p9;
    BOOL *flag,*p11;
    clock_t start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    out_pos=imc->out_pos;
    in_pos=imc->in_pos;
    flag=head->flag_max;
    n0=imc->n;
    
    // MARK: solve qualitative maximum reachability
    start_t=clock();
    printf("Solve qualitative maximum reachability:\n");
    
    if(!imc->queue)
    {
        imc->queue=p7=p8=queue=(uint32_t*)malloc(n0*sizeof(uint32_t));
    }
    else{p7=p8=queue=imc->queue;}
    // Enqueue label==1 with in_deg>0
    for(p11=flag,cnt1=0;cnt1!=n0;++cnt1,++p11)
        if(*p11&&*(in_pos+cnt1))*p8++=cnt1;
    // Pre^*(B)
    for(imc->l3=0,p9=p8;p7!=p8;++p7)
        for(p4=*(in_pos+*p7);p4->x1!=n0;++p4)
            if(!*(flag+p4->x1))
            {
                *(flag+p4->x1)=3;
                if(*(in_pos+p4->x1))*p8++=p4->x1;else ++imc->l3;
            }
    imc->l3+=p8-p9;
    // Enqueue label==0 with in_deg>0
    p7=p8=queue;p11=flag;cnt1=imc->l0=0;
    for(;cnt1!=n0;++cnt1,++p11)
        if(!*p11)
        {if(*(in_pos+cnt1))*p8++=cnt1;else ++imc->l0;}
        else if(*p11==3)
        {
            p2=p3=*(out_pos+cnt1);
            for(p2->p_u=p2->p=0.0;p3->next;)
            {
                p3+=p3->next;
                sum_p(&p2->p_u,&p2->p,p3->p_u);
//                p2->p_u+=p3->p_u;
            }
        }
    imc->l0+=p8-queue;
    // Pre_2^*(V/Pre^*(B))
    for(imc->l2=0,p9=p8;p7!=p8;++p7)
        for(p4=*(in_pos+*p7);p4->x1!=n0;++p4)
            if(*(flag+p4->x1)==3)
            {
                p2=p3=*(out_pos+p4->x1);
                p3+=p4->pos;
                if(p3->p_l==0.0)
                {
                    sum_m(&p2->p_u,&p2->p,p3->p_u);
//                    p2->p_u-=p3->p_u;
                    if(p2->p_u>=1.0)continue;
                }
                *(flag+p4->x1)=2;
                if(*(in_pos+p4->x1))*p8++=p4->x1;else ++imc->l2;
            }
    imc->l2+=p8-p9;
    imc->l3-=imc->l2;
    head->l2_max=imc->l2;
    printf("# of l1 = %u;\n# of l3 = %u;\n# of l0 = %u;\n# of l2 = %u.\n",imc->l1,imc->l3,imc->l0,imc->l2);
    cnt1=imc->l1+imc->l3+imc->l0+imc->l2;
    printf("l1+l3+l0+l2 = %u, n0 = %u.\n",cnt1,n0);
//    free(in_pos);imc->in_pos=0;
//    free(imc->in_edge);imc->in_edge=0;
    end_t=clock();
    printf("Time used to solve qualitative maximum reachability = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void solve_qualitative_min_reachability(HEAD *head)
{
    IMC *imc;
    uint32_t n0,cnt1;
    OUT_EDGE **out_pos,*p2,*p3;
    IN_EDGE **in_pos,*p4;
    uint32_t *queue,*p7,*p8,*p9;
    BOOL *flag,*p11;
    clock_t start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    out_pos=imc->out_pos;
    in_pos=imc->in_pos;
    flag=head->flag_min;
    n0=imc->n;
    
    // MARK: solve qualitative minimum reachability
    start_t=clock();
    printf("Solve qualitative minimum reachability:\n");
    
    if(!imc->queue)
    {
        imc->queue=p7=p8=queue=(uint32_t*)malloc(n0*sizeof(uint32_t));
    }
    else{p7=p8=queue=imc->queue;}
    // Enqueue label==1 with in_deg>0
    for(p11=flag,cnt1=0;cnt1!=n0;++cnt1,++p11)
        if(*p11)
        {if(*(in_pos+cnt1))*p8++=cnt1;}
        else
        {
            p2=p3=*(out_pos+cnt1);
            for(p2->p_u=p2->p=0.0;p3->next;)
            {
                p3+=p3->next;
                sum_p(&p2->p_u,&p2->p,p3->p_u);
//                p2->p_u+=p3->p_u;
            }
        }
    // Pre_2^*(B)
    for(imc->l3=0,p9=p8;p7!=p8;++p7)
        for(p4=*(in_pos+*p7);p4->x1!=n0;++p4)
            if(!*(flag+p4->x1))
            {
                p2=p3=*(out_pos+p4->x1);
                p3+=p4->pos;
                if(p3->p_l==0.0)
                {
                    sum_m(&p2->p_u,&p2->p,p3->p_u);
//                    p2->p_u-=p3->p_u;
                    if(p2->p_u>=1.0)continue;
                }
                *(flag+p4->x1)=3;
                if(*(in_pos+p4->x1))*p8++=p4->x1;else ++imc->l3;
            }
    imc->l3+=p8-p9;
    // Enqueue label==0 with in_deg>0
    for(p7=p8=queue,p11=flag,cnt1=imc->l0=0;cnt1!=n0;++cnt1,++p11)
        if(!*p11)
        {if(*(in_pos+cnt1))*p8++=cnt1;else ++imc->l0;}
    imc->l0+=p8-queue;
    // Pre^*(V/Pre_2^*(B))
    for(imc->l2=0,p9=p8;p7!=p8;++p7)
        for(p4=*(in_pos+*p7);p4->x1!=n0;++p4)
            if(*(flag+p4->x1)==3)
            {
                *(flag+p4->x1)=2;
                if(*(in_pos+p4->x1))*p8++=p4->x1;else ++imc->l2;
            }
    imc->l2+=p8-p9;
    imc->l3-=imc->l2;
    head->l2_min=imc->l2;
    printf("# of l1 = %u;\n# of l3 = %u;\n# of l0 = %u;\n# of l2 = %u.\n",imc->l1,imc->l3,imc->l0,imc->l2);
    cnt1=imc->l1+imc->l3+imc->l0+imc->l2;
    printf("l1+l3+l0+l2 = %u, n0 = %u.\n",cnt1,n0);
//    free(in_pos);imc->in_pos=0;
//    free(imc->in_edge);imc->in_edge=0;
    end_t=clock();
    printf("Time used to solve qualitative minimum reachability = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void solve_quantitative_max_reachability_power_method(HEAD *head)
{
    IMC *imc;
    uint32_t n0,l2,cnt2,cnt3;
    uint32_t i,j;
    uint64_t cnt1;
    OUT_EDGE **out_pos,**sort_edge,*p2,*p3,*p4,**p16,**p17,**p18;
    uint32_t *encode_max,*decode_max,*p5,*p6,*p7,*p8;
    double err1,err2,p_tmp,p_tmp1,*x_vec,*b_vec,*p11,*p12,*p13,*x_current,*x_next,*x_tmp,err_current,err_max = 0.0,err_max1=1.0,**sort_x,**p14,**p15;
    BOOL *flag,*p9,tag;
    clock_t start_t0,start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    out_pos=imc->out_pos;
    flag=head->flag_max;
    n0=imc->n;
    l2=head->l2_max;
    
    printf("Solve quantitative maximum reachability using power method:\n");
    
    // MARK: build data structure for iterative method
    start_t0=start_t=clock();
    printf("Build data structure for iterative method:\n");
    if(!l2)
    {
        printf("All states have trivial probability 0 or 1, so no quantitative maximum reachability needs to be solved.\n");
        return;
    }
    // Encode and decode
    if(head->encode_max)
    {
        encode_max=head->encode_max;
        decode_max=head->decode_max;
        p8=decode_max+l2;
    }
    else
    {
        head->encode_max=encode_max=imc->queue;imc->queue=0;
        head->decode_max=decode_max=(uint32_t*)malloc(l2*sizeof(uint32_t));
        p5=encode_max;p7=decode_max;p9=flag;
        for(p6=p5+n0;p5!=p6;++p5,++p9)
            if(*p9==2)
            {
                *p5=(uint32_t)(p7-decode_max);
                *p7=(uint32_t)(p5-encode_max);++p7;
            }
            else *p5=n0;
    }
    // Compute sum_l and sum_u
    for(p7=decode_max,p8=p7+l2;p7!=p8;++p7)
    {
        p2=p4=*(out_pos+*p7);
        for(p2->p=p2->p_l=p2->p_u=err1=err2=0.0;p4->next;)
        {
            p4+=p4->next;
            sum_p(&p2->p_l,&err1,p4->p_l);
            sum_p(&p2->p_u,&err2,p4->p_u);
//            p2->p_l+=p4->p_l;
//            p2->p_u+=p4->p_u;
        }
        // Sterbenz's lemma
        if(1.0<=p2->p_l*2)p2->p_l=(1.0-p2->p_l)-err1;
        else
        {
            p_tmp=p2->p_l;p_tmp1=0.0;p2->p_l=1.0;
            sum_m(&p2->p_l,&p_tmp1,p_tmp);
            sum_m(&p2->p_l,&p_tmp1,err1);
        }
        sum_m(&p2->p_u,&err2,1.0);
        sum_p(&p2->p_u,&p2->p,err2);
//        p2->p_l=1.0-p2->p_l;p2->p_u-=1.0;
    }
    // Set up x = Ax + b
    p11=imc->b_vec=b_vec=(double*)calloc(l2,sizeof(double));
    for(p7=decode_max,cnt1=0;p7!=p8;++p7,++p11)
    {
        p2=p3=p4=*(out_pos+*p7);
        err2=p2->p;
        err1=p2->p=0.0;
        for(p2->num=tag=0;p4->next;)
        {
            p4+=p4->next;
            p9=flag+p4->x2;
            if(*p9==2)
            {p3=p4;++p2->num;p4->x2=*(encode_max+p4->x2);}
            else
            {
                p3->next+=p4->next;
                if(*p9&1)// label == 1 || 3
                {
                    switch(tag)
                    {
                        case 0:
                        {
                            sum_p(&p2->p_l,&err1,p4->p_l);
                            if(p2->p_l>p4->p_u)
                            {
                                sum_p(p11,&p2->p,p4->p_u);
                                sum_m(&p2->p_l,&err1,p4->p_u);
                            }
                            else
                            {
                                sum_p(p11,&p2->p,p2->p_l);
                                sum_p(p11,&p2->p,err1);
                                tag=1;
                            }
//                            p_tmp=p4->p_u-p4->p_l;
//                            if(p2->p_l>p_tmp)
//                            {
//                                *p11+=p4->p_u;
//                                p2->p_l-=p_tmp;
//                            }
//                            else
//                            {*p11+=p4->p_l+p2->p_l;tag=1;}
                        }
                        break;
                        case 1:
                        sum_p(p11,&p2->p,p4->p_l);
//                        *p11+=p4->p_l;
                        break;
                        case 2:
                        sum_p(p11,&p2->p,p4->p_u);
//                        *p11+=p4->p_u;
                    }
                }
                else if(!tag)
                {
                    sum_p(&p2->p_u,&err2,p4->p_l);
                    if(p2->p_u>p4->p_u)
                    sum_m(&p2->p_u,&err2,p4->p_u);
                    else tag=2;
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p_u>p_tmp)
//                    {p2->p_u-=p_tmp;}
//                    else{tag=2;}
                }
            }
        }
        if(p3!=p2)p3->next=0;else p2=0;
        if(!p2)continue;
        cnt1+=p2->num;
        if(tag)
        {
            p2->p_u=0.0;
            if(tag&1)
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_l;}
            else
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_u;}
        }else{p2->p_l=err2;}
    }
    printf("Size of iteration matrix = n + m = %u + %llu = %llu.\n",l2,cnt1,l2+cnt1);
    printf("Size of sort_edge = %llu.\n",cnt1);
    imc->x_vec=x_vec=(double*)malloc((l2<<1)*sizeof(double));//l2*2
    if(imc->sort_x)sort_x=imc->sort_x;
    else
    {
        imc->sort_x=sort_x=(double**)malloc(l2*sizeof(double*));
    }
    // x(0)=0, x(1)=b
    p11=b_vec;p12=p11+l2;p13=x_vec;p14=sort_x;
    for(;p11!=p12;++p11,++p13,++p14)
    {*p13=*p11;*p14=p13;}
    x_current=x_vec;x_next=x_vec+l2;
    // Sort x(1)
    qsort(sort_x,l2,sizeof(double*),cmp1);
    if(!permutation)
    permutation=(uint32_t*)malloc(l2*sizeof(uint32_t));
    for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
        *(*p14-x_vec+permutation)=cnt2;
    
    p16=p17=imc->sort_edge=sort_edge=(OUT_EDGE**)malloc(cnt1*sizeof(OUT_EDGE*));
    // assign probability to edges
    for(p7=decode_max;p7!=p8;++p7)
    {
        p2=p4=*(out_pos+*p7);
        if(!p2)continue;
        for(;p4->next;++p17)
        {p4+=p4->next;*p17=p4;}
        qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
        if(p2->p_u==0.0){p16=p17;continue;}
        for(p_tmp1=p2->p_u,err2=p2->p_l,tag=0;p16!=p17;++p16)
        {
            p4=*p16;
            if(tag)p4->p=p4->p_u;
            else
            {
                p_tmp=p_tmp1;err1=err2;
                sum_p(&p_tmp1,&err2,p4->p_l);
                if(p_tmp1>p4->p_u)
                {
                    p4->p=p4->p_l;
                    sum_m(&p_tmp1,&err2,p4->p_u);
                }
                else
                {
                    p4->p=p4->p_u;err2=0;
                    sum_m(&p4->p,&err2,p_tmp);
                    sum_m(&p4->p,&err2,err1);
                    tag=2;
                }
//                p_tmp=p4->p_u-p4->p_l;
//                if(p2->p>p_tmp)
//                {
//                    p4->p=p4->p_l;
//                    p2->p-=p_tmp;
//                }
//                else{p4->p=p4->p_u-p2->p;tag=2;}
            }
        }
    }
    end_t=clock();
    printf("Time used to build data structure for iterative method = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    
    // MARK: Solve x = Ax + b
    start_t=clock();
    printf("Solve x = Ax + b:\n");
    for(cnt3=0,j=1;;++j)
    {
        for(i=1;i<=ITERATION_BOUND;++i)
        {
            p7=decode_max;p11=b_vec;
            p16=p17=sort_edge;
            p12=x_current;p13=x_next;
            err_max=0.0;;cnt2=0;
            for(;p7!=p8;++p7,++p11,++p12,++p13)
            {
                p4=*(out_pos+*p7);
                if(!p4){*p13=*p11;continue;}
                for(*p13=p4->p,err2=0.0,p17=p16+p4->num;p16!=p17;++p16)
                {
                    p_tmp=*(x_current+(*p16)->x2)*(*p16)->p;
                    sum_p(p13,&err2,p_tmp);
                }
                sum_p(p13,&err2,*p11);
                
//                p_tmp=*p13*EPS;
//                sum_p(p13,&err2,p_tmp);
                
                
//                for(*p13=0,p17=p16+p4->num;p16!=p17;++p16)
//                    *p13+=*(x_current+(*p16)->x2)*(*p16)->p;
//                *p13+=*p11;
                
                
                if(*p13+*p13*MACHINE_EPSILON<*p12)printf("Unexpected, not monotone increasing: node[%u]: x_current: %.17e difference: %.3e.\n",*p7,*p12,(*p12-*p13)/MACHINE_EPSILON);
                
                if(*p13<*p12)++cnt2;
                
//                if(*p13<*p12)*p13=*p12;
                
                err_current=fabs(*p13-*p12);
                if(err_current>err_max)err_max=err_current;
            }
            
//            if(cnt2)
//            printf("#: %u\t",cnt2);
            //swap x_current and x_next
            x_tmp=x_current;
            x_current=x_next;
            x_next=x_tmp;
            if(i==1)
            {
                printf("Error_max after shift = %.17e.\t",err_max);
                printf("#: %u\t",cnt2);
            }
            
            if(err_max1<err_max)printf("Inner # %u: relative error violation: %.17e, current error: %.17e, previous error: %.17e.\n",i,(err_max-err_max1)/err_max,err_max,err_max1);
            err_max1=err_max;
            
            if(err_max<=EPSILON)break;
        }
        printf("%u th iteration: ",j);
        if(i<=ITERATION_BOUND)printf("# of iterations: %u.",i);
        else printf("# of iterations exceeds ITERATION_BOUND %u.",ITERATION_BOUND);
        printf("\t err_max = %.17e.",err_max);
        cnt3+=i;
        if(i>ITERATION_BOUND)--cnt3;
        for(p14=sort_x,p15=p14+l2,p11=*p14,++p14;p14!=p15;++p14)
        {
            p12=*p14;
            if(*p11<=*p12)p11=p12;
            else break;
        }
        printf("\t%u\n",(uint32_t)(p14-sort_x));
        if(p14==p15)
        {
            if(i>ITERATION_BOUND){printf("Order doesn't change but needs more iterations.\n");continue;}
            else break;
        }
        
        qsort(sort_x,l2,sizeof(double*),cmp1);
        for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
            *(*p14-x_vec+permutation)=cnt2;
        // assign probability to edges
        p16=p17=sort_edge;
        for(p7=decode_max;p7!=p8;++p7)
        {
            p2=*(out_pos+*p7);
            if(!p2)continue;
            if(p2->p_u==0.0)
            {p16=p17+=p2->num;continue;}
            for(p18=p17+p2->num,p3=*p17,++p17;p17!=p18;++p17)
            {
                p4=*p17;
                if(*(permutation+p3->x2)<*(permutation+p4->x2))p3=p4;
                else break;
            }
            if(p17==p18){p16=p18;continue;}
            else p17=p18;
            qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
            for(p_tmp1=p2->p_u,err2=p2->p_l,tag=0;p16!=p17;++p16)
            {
                p4=*p16;
                if(tag)p4->p=p4->p_u;
                else
                {
                    p_tmp=p_tmp1;err1=err2;
                    sum_p(&p_tmp1,&err2,p4->p_l);
                    if(p_tmp1>p4->p_u)
                    {
                        p4->p=p4->p_l;
                        sum_m(&p_tmp1,&err2,p4->p_u);
                    }
                    else
                    {
                        p4->p=p4->p_u;err2=0;
                        sum_m(&p4->p,&err2,p_tmp);
                        sum_m(&p4->p,&err2,err1);
                        tag=2;
                    }
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p>p_tmp)
//                    {
//                        p4->p=p4->p_l;
//                        p2->p-=p_tmp;
//                    }
//                    else{p4->p=p4->p_u-p2->p;tag=2;}
                }
            }
        }
    }
    
    printf("# of outer loop iterations :%u\n",j);
    printf("# of total loop iterations :%u\n",cnt3);
    
    for(p11=b_vec,p12=p11+l2,p13=x_current;p11!=p12;++p11,++p13)
        *p11=*p13;
    head->x_vec_power_max=b_vec;
    imc->b_vec=0;
    free(x_vec);imc->x_vec=0;
    free(sort_edge);imc->sort_edge=0;
    
    
//    free(out_pos);imc->out_pos=0;
//    free(imc->out_edge);imc->out_edge=0;
//    free(decode1);head->decode1=0;
//    free(b_vec);imc->b_vec=0;
    end_t=clock();
    printf("Time used to solve x = Ax + b = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("Time used to solve quantitative maximum reachability using power method = %.4f\n",
           (double)(end_t-start_t0)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void solve_quantitative_max_reachability_Jacobi_method(HEAD *head)
{
    IMC *imc;
    uint32_t n0,l2,cnt2,cnt3;
    uint32_t i,j;
    uint64_t cnt1;
    OUT_EDGE **out_pos,**sort_edge,*p2,*p3,*p4,**p16,**p17,**p18;
    uint32_t *encode_max,*decode_max,*p5,*p6,*p7,*p8;
    double err1,err2,p_tmp,p_tmp1,*x_vec,*b_vec,*p11,*p12,*p13,*x_current,*x_next,*x_tmp,err_current,err_max = 0.0,**sort_x,**p14,**p15;
    BOOL *flag,*p9,tag;
    clock_t start_t0,start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    out_pos=imc->out_pos;
    flag=head->flag_max;
    n0=imc->n;
    l2=head->l2_max;
    
    printf("Solve quantitative maximum reachability using Jacobi method:\n");
    
    // MARK: build data structure for iterative method
    start_t0=start_t=clock();
    printf("Build data structure for iterative method:\n");
    if(!l2)
    {
        printf("All states have trivial probability 0 or 1, so no quantitative maximum reachability needs to be solved.\n");
        return;
    }
    // Encode and decode
    if(head->encode_max)
    {
        encode_max=head->encode_max;
        decode_max=head->decode_max;
        p8=decode_max+l2;
    }
    else
    {
        head->encode_max=encode_max=imc->queue;imc->queue=0;
        head->decode_max=decode_max=(uint32_t*)malloc(l2*sizeof(uint32_t));
        p5=encode_max;p7=decode_max;p9=flag;
        for(p6=p5+n0;p5!=p6;++p5,++p9)
            if(*p9==2)
            {
                *p5=(uint32_t)(p7-decode_max);
                *p7=(uint32_t)(p5-encode_max);++p7;
            }
            else *p5=n0;
    }
    // Compute sum_l and sum_u
    for(p7=decode_max,p8=p7+l2;p7!=p8;++p7)
    {
        p2=p4=*(out_pos+*p7);
        for(p2->p=p2->p_l=p2->p_u=err1=err2=0.0;p4->next;)
        {
            p4+=p4->next;
            sum_p(&p2->p_l,&err1,p4->p_l);
            sum_p(&p2->p_u,&err2,p4->p_u);
//            p2->p_l+=p4->p_l;
//            p2->p_u+=p4->p_u;
        }
        // Sterbenz's lemma
        if(1.0<=p2->p_l*2)p2->p_l=(1.0-p2->p_l)-err1;
        else
        {
            p_tmp=p2->p_l;p_tmp1=0.0;p2->p_l=1.0;
            sum_m(&p2->p_l,&p_tmp1,p_tmp);
            sum_m(&p2->p_l,&p_tmp1,err1);
        }
        sum_m(&p2->p_u,&err2,1.0);
        sum_p(&p2->p_u,&p2->p,err2);
//        p2->p_l=1.0-p2->p_l;p2->p_u-=1.0;
    }
    // Set up (I-D)x = (L+U)x + b
    p11=imc->b_vec=b_vec=(double*)calloc(l2,sizeof(double));
    for(p7=decode_max,cnt1=0;p7!=p8;++p7,++p11)
    {
        p2=p3=p4=*(out_pos+*p7);
        err2=p2->p;
        err1=p2->p=0.0;
        for(p2->x2=p2->num=tag=0;p4->next;)
        {
            p4+=p4->next;
            p9=flag+p4->x2;
            if(*p9==2)
            {
                p3=p4;++p2->num;
                if(*p7==p4->x2)p2->x2=(uint32_t)(p4-p2);
                p4->x2=*(encode_max+p4->x2);
            }
            else
            {
                p3->next+=p4->next;
                if(*p9&1)// label == 1 || 3
                {
                    switch(tag)
                    {
                        case 0:
                        {
                            sum_p(&p2->p_l,&err1,p4->p_l);
                            if(p2->p_l>p4->p_u)
                            {
                                sum_p(p11,&p2->p,p4->p_u);
                                sum_m(&p2->p_l,&err1,p4->p_u);
                            }
                            else
                            {
                                sum_p(p11,&p2->p,p2->p_l);
                                sum_p(p11,&p2->p,err1);
                                tag=1;
                            }
//                            p_tmp=p4->p_u-p4->p_l;
//                            if(p2->p_l>p_tmp)
//                            {
//                                *p11+=p4->p_u;
//                                p2->p_l-=p_tmp;
//                            }
//                            else
//                            {*p11+=p4->p_l+p2->p_l;tag=1;}
                        }
                        break;
                        case 1:
                        sum_p(p11,&p2->p,p4->p_l);
//                        *p11+=p4->p_l;
                        break;
                        case 2:
                        sum_p(p11,&p2->p,p4->p_u);
//                        *p11+=p4->p_u;
                    }
                }
                else if(!tag)
                {
                    sum_p(&p2->p_u,&err2,p4->p_l);
                    if(p2->p_u>p4->p_u)
                    sum_m(&p2->p_u,&err2,p4->p_u);
                    else tag=2;
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p_u>p_tmp)
//                    {p2->p_u-=p_tmp;}
//                    else{tag=2;}
                }
            }
        }
        if(p3!=p2)p3->next=0;else p2=0;
        if(!p2)continue;
        cnt1+=p2->num;
        if(tag)
        {
            p2->p_u=0.0;
            if(tag&1)
            {
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_l;}
                if(p2->x2)
                {p4=p2+p2->x2;p4->p=1.0/(1.0-p4->p_l);}
            }
            else
            {
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_u;}
                if(p2->x2)
                {p4=p2+p2->x2;p4->p=1.0/(1.0-p4->p_u);}
            }
        }else{p2->p_l=err2;}
    }
    printf("Size of iteration matrix = n + m = %u + %llu = %llu.\n",l2,cnt1,l2+cnt1);
    printf("Size of sort_edge = %llu.\n",cnt1);
    imc->x_vec=x_vec=(double*)malloc((l2<<1)*sizeof(double));//l2*2
    if(imc->sort_x)sort_x=imc->sort_x;
    else
    {
        imc->sort_x=sort_x=(double**)malloc(l2*sizeof(double*));
    }
    // x(0)=0, x(1)=b(for sort)
    p11=b_vec;p12=p11+l2;p13=x_vec;p14=sort_x;
    for(;p11!=p12;++p11,++p13,++p14)
    {*p13=*p11;*p14=p13;}
    x_current=x_vec;x_next=x_vec+l2;
    // Sort x(1)
    qsort(sort_x,l2,sizeof(double*),cmp1);
    if(!permutation)
    permutation=(uint32_t*)malloc(l2*sizeof(uint32_t));
    for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
        *(*p14-x_vec+permutation)=cnt2;
    
    p16=p17=imc->sort_edge=sort_edge=(OUT_EDGE**)malloc(cnt1*sizeof(OUT_EDGE*));
    // assign probability to edges, x(1)=(I-D)^{-1}b
    for(p7=decode_max,p13=x_vec;p7!=p8;++p7,++p13)
    {
        p2=p4=*(out_pos+*p7);
        if(!p2)continue;
        for(;p4->next;++p17)
        {p4+=p4->next;*p17=p4;}
        qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
        if(p2->p_u==0.0)
        {
            p16=p17;
            if(p2->x2)
            {
                p4=p2+p2->x2;*p13*=p4->p;
                err2=p2->p*p4->p;*p13+=err2;
            }
            continue;
        }
        for(p_tmp1=p2->p_u,err2=p2->p_l,tag=0;p16!=p17;++p16)
        {
            p4=*p16;
            if(tag)p4->p=p4->p_u;
            else
            {
                p_tmp=p_tmp1;err1=err2;
                sum_p(&p_tmp1,&err2,p4->p_l);
                if(p_tmp1>p4->p_u)
                {
                    p4->p=p4->p_l;
                    sum_m(&p_tmp1,&err2,p4->p_u);
                }
                else
                {
                    p4->p=p4->p_u;err2=0;
                    sum_m(&p4->p,&err2,p_tmp);
                    sum_m(&p4->p,&err2,err1);
                    tag=2;
                }
//                p_tmp=p4->p_u-p4->p_l;
//                if(p2->p>p_tmp)
//                {
//                    p4->p=p4->p_l;
//                    p2->p-=p_tmp;
//                }
//                else{p4->p=p4->p_u-p2->p;tag=2;}
            }
        }
        if(p2->x2)
        {
            p4=p2+p2->x2;
            p4->p=1.0/(1-p4->p);
            *p13*=p4->p;
            err2=p2->p*p4->p;*p13+=err2;
        }
    }
    end_t=clock();
    printf("Time used to build data structure for iterative method = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    
    // MARK: Solve (I-D)x = (L+U)x + b
    start_t=clock();
    printf("Solve (I-D)x = (L+U)x + b:\n");
    for(cnt3=0,j=1;;++j)
    {
        for(i=1;i<=ITERATION_BOUND;++i)
        {
            p7=decode_max;p11=b_vec;
            p16=p17=sort_edge;
            p12=x_current;p13=x_next;
            err_max=0.0;
            for(;p7!=p8;++p7,++p11,++p12,++p13)
            {
                p2=p4=*(out_pos+*p7);
                if(!p4){*p13=*p11;continue;}
                if(p2->x2)
                {
                    p3=p2+p2->x2;
                    *p13=p4->p;err2=0.0;p17=p16+p4->num;
                    for(;p16!=p17;++p16)
                        if(*p16!=p3)
                        {
                            p_tmp=*(x_current+(*p16)->x2)*(*p16)->p;
                            sum_p(p13,&err2,p_tmp);
                        }
                    sum_p(p13,&err2,*p11);
                    *p13*=p3->p;err2*=p3->p;*p13+=err2;
                    
//                    p3=p2+p2->x2;
//                    *p13=0;p17=p16+p4->num;
//                    for(;p16!=p17;++p16)
//                        if(*p16!=p3)*p13+=*(x_current+(*p16)->x2)*(*p16)->p;
//                    *p13+=*p11;*p13*=p3->p;
                }
                else
                {
                    *p13=p4->p;err2=0.0;p17=p16+p4->num;
                    for(;p16!=p17;++p16)
                    {
                        p_tmp=*(x_current+(*p16)->x2)*(*p16)->p;
                        sum_p(p13,&err2,p_tmp);
                    }
                    sum_p(p13,&err2,*p11);
                    
//                    *p13=0;p17=p16+p4->num;
//                    for(;p16!=p17;++p16)
//                    *p13+=*(x_current+(*p16)->x2)*(*p16)->p;
//                    *p13+=*p11;
                }
                
                if(*p13+8*MACHINE_EPSILON<*p12)printf("Unexpected, not monotone increasing: node[%u]: x_current: %.17e difference: %.3e.\n",*p7,*p12        ,(*p12-*p13)/MACHINE_EPSILON);
                
//                if(*p13<*p12)*p13=*p12;
                
                err_current=fabs(*p13-*p12);
                if(err_current>err_max)err_max=err_current;
            }
            //swap x_current and x_next
            x_tmp=x_current;
            x_current=x_next;
            x_next=x_tmp;
            if(i==1)printf("Error_max after shift = %.17e.\t",err_max);
            if(err_max<=EPSILON)break;
        }
        printf("%u th iteration: ",j);
        if(i<=ITERATION_BOUND)printf("# of iterations: %u.",i);
        else printf("# of iterations exceeds ITERATION_BOUND %u.",ITERATION_BOUND);
        printf("\t err_max = %.17e.\n",err_max);
        cnt3+=i;
        if(i>ITERATION_BOUND)--cnt3;
        for(p14=sort_x,p15=p14+l2,p11=*p14,++p14;p14!=p15;++p14)
        {
            p12=*p14;
//            if(*p11<=*p12+MACHINE_EPSILON)p11=p12;
            if(*p11<=*p12)p11=p12;
            else break;
        }
        printf("\t%u\n",(uint32_t)(p14-sort_x));
        if(p14==p15)
        {
            if(i>ITERATION_BOUND){printf("Order doesn't change but needs more iterations.\n");continue;}
            else break;
        }
        
        qsort(sort_x,l2,sizeof(double*),cmp1);
        for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
            *(*p14-x_vec+permutation)=cnt2;
        // assign probability to edges
        p16=p17=sort_edge;
        for(p7=decode_max;p7!=p8;++p7)
        {
            p2=*(out_pos+*p7);
            if(!p2)continue;
            if(p2->p_u==0.0)
            {p16=p17+=p2->num;continue;}
            for(p18=p17+p2->num,p3=*p17,++p17;p17!=p18;++p17)
            {
                p4=*p17;
                if(*(permutation+p3->x2)<*(permutation+p4->x2))p3=p4;
                else break;
            }
            if(p17==p18){p16=p18;continue;}
            else p17=p18;
            qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
            for(p_tmp1=p2->p_u,err2=p2->p_l,tag=0;p16!=p17;++p16)
            {
                p4=*p16;
                if(tag)p4->p=p4->p_u;
                else
                {
                    p_tmp=p_tmp1;err1=err2;
                    sum_p(&p_tmp1,&err2,p4->p_l);
                    if(p_tmp1>p4->p_u)
                    {
                        p4->p=p4->p_l;
                        sum_m(&p_tmp1,&err2,p4->p_u);
                    }
                    else
                    {
                        p4->p=p4->p_u;err2=0;
                        sum_m(&p4->p,&err2,p_tmp);
                        sum_m(&p4->p,&err2,err1);
                        tag=2;
                    }
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p>p_tmp)
//                    {
//                        p4->p=p4->p_l;
//                        p2->p-=p_tmp;
//                    }
//                    else{p4->p=p4->p_u-p2->p;tag=2;}
                }
            }
            if(p2->x2)
            {p4=p2+p2->x2;p4->p=1.0/(1-p4->p);}
        }
    }
    
    printf("# of outer loop iterations :%u\n",j);
    printf("# of total loop iterations :%u\n",cnt3);
    
    for(p11=b_vec,p12=p11+l2,p13=x_current;p11!=p12;++p11,++p13)
        *p11=*p13;
    head->x_vec_Jacobi_max=b_vec;
    imc->b_vec=0;
    free(x_vec);imc->x_vec=0;
    free(sort_edge);imc->sort_edge=0;
    
    
//    free(out_pos);imc->out_pos=0;
//    free(imc->out_edge);imc->out_edge=0;
//    free(decode1);head->decode1=0;
//    free(b_vec);imc->b_vec=0;
    end_t=clock();
    printf("Time used to solve (I-D)x = (L+U)x + b = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("Time used to solve quantitative maximum reachability using Jacobi method = %.4f\n",
           (double)(end_t-start_t0)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void solve_quantitative_max_reachability_Gauss_Seidel_method(HEAD *head)
{
    IMC *imc;
    uint32_t n0,l2,cnt2,cnt3;
    uint32_t i,j;
    uint64_t cnt1;
    OUT_EDGE **out_pos,**sort_edge,*p2,*p3,*p4,**p16,**p17,**p18;
    uint32_t *encode_max,*decode_max,*p5,*p6,*p7,*p8;
    double err1,err2,p_tmp,p_tmp1,*x_vec,*b_vec,*p11,*p12,*p13,x_current,err_current,err_max = 0.0,**sort_x,**p14,**p15;
    BOOL *flag,*p9,tag;
    clock_t start_t0,start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    out_pos=imc->out_pos;
    flag=head->flag_max;
    n0=imc->n;
    l2=head->l2_max;
    
    printf("Solve quantitative maximum reachability using Gauss Seidel method:\n");
    
    // MARK: build data structure for iterative method
    start_t0=start_t=clock();
    printf("Build data structure for iterative method:\n");
    if(!l2)
    {
        printf("All states have trivial probability 0 or 1, so no quantitative maximum reachability needs to be solved.\n");
        return;
    }
    // Encode and decode
    if(head->encode_max)
    {
        encode_max=head->encode_max;
        decode_max=head->decode_max;
        p8=decode_max+l2;
    }
    else
    {
        head->encode_max=encode_max=imc->queue;imc->queue=0;
        head->decode_max=decode_max=(uint32_t*)malloc(l2*sizeof(uint32_t));
        p5=encode_max;p7=decode_max;p9=flag;
        for(p6=p5+n0;p5!=p6;++p5,++p9)
            if(*p9==2)
            {
                *p5=(uint32_t)(p7-decode_max);
                *p7=(uint32_t)(p5-encode_max);++p7;
            }
            else *p5=n0;
    }
    // Compute sum_l and sum_u
    for(p7=decode_max,p8=p7+l2;p7!=p8;++p7)
    {
        p2=p4=*(out_pos+*p7);
        for(p2->p=p2->p_l=p2->p_u=err1=err2=0.0;p4->next;)
        {
            p4+=p4->next;
            sum_p(&p2->p_l,&err1,p4->p_l);
            sum_p(&p2->p_u,&err2,p4->p_u);
//            p2->p_l+=p4->p_l;
//            p2->p_u+=p4->p_u;
        }
        // Sterbenz's lemma
        if(1.0<=p2->p_l*2)p2->p_l=(1.0-p2->p_l)-err1;
        else
        {
            p_tmp=p2->p_l;p_tmp1=0.0;p2->p_l=1.0;
            sum_m(&p2->p_l,&p_tmp1,p_tmp);
            sum_m(&p2->p_l,&p_tmp1,err1);
        }
        sum_m(&p2->p_u,&err2,1.0);
        sum_p(&p2->p_u,&p2->p,err2);
//        p2->p_l=1.0-p2->p_l;p2->p_u-=1.0;
    }
    // Set up (I-D-L)x = Ux + b
    p11=imc->b_vec=b_vec=(double*)calloc(l2,sizeof(double));
    for(p7=decode_max,cnt1=0;p7!=p8;++p7,++p11)
    {
        p2=p3=p4=*(out_pos+*p7);
        err2=p2->p;
        err1=p2->p=0.0;
        for(p2->x2=p2->num=tag=0;p4->next;)
        {
            p4+=p4->next;
            p9=flag+p4->x2;
            if(*p9==2)
            {
                p3=p4;++p2->num;
                if(*p7==p4->x2)p2->x2=(uint32_t)(p4-p2);
                p4->x2=*(encode_max+p4->x2);
            }
            else
            {
                p3->next+=p4->next;
                if(*p9&1)// label == 1 || 3
                {
                    switch(tag)
                    {
                        case 0:
                        {
                            sum_p(&p2->p_l,&err1,p4->p_l);
                            if(p2->p_l>p4->p_u)
                            {
                                sum_p(p11,&p2->p,p4->p_u);
                                sum_m(&p2->p_l,&err1,p4->p_u);
                            }
                            else
                            {
                                sum_p(p11,&p2->p,p2->p_l);
                                sum_p(p11,&p2->p,err1);
                                tag=1;
                            }
//                            p_tmp=p4->p_u-p4->p_l;
//                            if(p2->p_l>p_tmp)
//                            {
//                                *p11+=p4->p_u;
//                                p2->p_l-=p_tmp;
//                            }
//                            else
//                            {*p11+=p4->p_l+p2->p_l;tag=1;}
                        }
                        break;
                        case 1:
                        sum_p(p11,&p2->p,p4->p_l);
//                        *p11+=p4->p_l;
                        break;
                        case 2:
                        sum_p(p11,&p2->p,p4->p_u);
//                        *p11+=p4->p_u;
                    }
                }
                else if(!tag)
                {
                    sum_p(&p2->p_u,&err2,p4->p_l);
                    if(p2->p_u>p4->p_u)
                    sum_m(&p2->p_u,&err2,p4->p_u);
                    else tag=2;
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p_u>p_tmp)
//                    {p2->p_u-=p_tmp;}
//                    else{tag=2;}
                }
            }
        }
        if(p3!=p2)p3->next=0;else p2=0;
        if(!p2)continue;
        cnt1+=p2->num;
        if(tag)
        {
            p2->p_u=0.0;
            if(tag&1)
            {
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_l;}
                if(p2->x2)
                {p4=p2+p2->x2;p4->p=1.0/(1-p4->p_l);}
            }
            else
            {
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_u;}
                if(p2->x2)
                {p4=p2+p2->x2;p4->p=1.0/(1-p4->p_u);}
            }
        }else{p2->p_l=err2;}
    }
    printf("Size of iteration matrix = n + m = %u + %llu = %llu.\n",l2,cnt1,l2+cnt1);
    printf("Size of sort_edge = %llu.\n",cnt1);
    imc->x_vec=x_vec=(double*)malloc(l2*sizeof(double));//l2
    if(imc->sort_x)sort_x=imc->sort_x;
    else
    {
        imc->sort_x=sort_x=(double**)malloc(l2*sizeof(double*));
    }
    // x(0)=0, x(1)=b(for sort)
    p11=b_vec;p12=p11+l2;p13=x_vec;p14=sort_x;
    for(;p11!=p12;++p11,++p13,++p14)
    {*p13=*p11;*p14=p13;}
    // Sort x(1)
    qsort(sort_x,l2,sizeof(double*),cmp1);
    if(!permutation)
    permutation=(uint32_t*)malloc(l2*sizeof(uint32_t));
    for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
        *(*p14-x_vec+permutation)=cnt2;
    
    p16=p17=imc->sort_edge=sort_edge=(OUT_EDGE**)malloc(cnt1*sizeof(OUT_EDGE*));
    // assign probability to edges, x(1)=(I-D)^{-1}b <= (I-D-L)^{-1}b
    for(p7=decode_max,p13=x_vec;p7!=p8;++p7,++p13)
    {
        p2=p4=*(out_pos+*p7);
        if(!p2)continue;
        for(;p4->next;++p17)
        {p4+=p4->next;*p17=p4;}
        qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
        if(p2->p_u==0.0)
        {
            p16=p17;
            if(p2->x2)
            {
                p4=p2+p2->x2;*p13*=p4->p;
                err2=p2->p*p4->p;*p13+=err2;
            }
            continue;
        }
        for(p_tmp1=p2->p_u,err2=p2->p_l,tag=0;p16!=p17;++p16)
        {
            p4=*p16;
            if(tag)p4->p=p4->p_u;
            else
            {
                p_tmp=p_tmp1;err1=err2;
                sum_p(&p_tmp1,&err2,p4->p_l);
                if(p_tmp1>p4->p_u)
                {
                    p4->p=p4->p_l;
                    sum_m(&p_tmp1,&err2,p4->p_u);
                }
                else
                {
                    p4->p=p4->p_u;err2=0;
                    sum_m(&p4->p,&err2,p_tmp);
                    sum_m(&p4->p,&err2,err1);
                    tag=2;
                }
//                p_tmp=p4->p_u-p4->p_l;
//                if(p2->p>p_tmp)
//                {
//                    p4->p=p4->p_l;
//                    p2->p-=p_tmp;
//                }
//                else{p4->p=p4->p_u-p2->p;tag=2;}
            }
        }
        if(p2->x2)
        {
            p4=p2+p2->x2;
            p4->p=1.0/(1-p4->p);
            *p13*=p4->p;
            err2=p2->p*p4->p;*p13+=err2;
        }
    }
    end_t=clock();
    printf("Time used to build data structure for iterative method = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    
    // MARK: Solve (I-D-L)x = Ux + b
    start_t=clock();
    printf("Solve (I-D-L)x = Ux + b:\n");
    for(cnt3=0,j=1;;++j)
    {
        for(i=1;i<=ITERATION_BOUND;++i)
        {
            p7=decode_max;p11=b_vec;
            p16=p17=sort_edge;
            p13=x_vec;
            err_max=0.0;
            for(;p7!=p8;++p7,++p11,++p12,++p13)
            {
                x_current=*p13;
                p2=p4=*(out_pos+*p7);
                if(!p4){*p13=*p11;continue;}
                if(p2->x2)
                {
                    p3=p2+p2->x2;
                    *p13=p4->p;err2=0.0;p17=p16+p4->num;
                    for(;p16!=p17;++p16)
                        if(*p16!=p3)
                        {
                            p_tmp=*(x_vec+(*p16)->x2)*(*p16)->p;
                            sum_p(p13,&err2,p_tmp);
                        }
                    sum_p(p13,&err2,*p11);
                    *p13*=p3->p;err2*=p3->p;*p13+=err2;
                    
//                    p3=p2+p2->x2;
//                    *p13=0;p17=p16+p4->num;
//                    for(;p16!=p17;++p16)
//                        if(*p16!=p3)*p13+=*(x_vec+(*p16)->x2)*(*p16)->p;
//                    *p13+=*p11;*p13*=p3->p;
                }
                else
                {
                    *p13=p4->p;err2=0.0;p17=p16+p4->num;
                    for(;p16!=p17;++p16)
                    {
                        p_tmp=*(x_vec+(*p16)->x2)*(*p16)->p;
                        sum_p(p13,&err2,p_tmp);
                    }
                    sum_p(p13,&err2,*p11);
                    
//                    *p13=0;p17=p16+p4->num;
//                    for(;p16!=p17;++p16)
//                    *p13+=*(x_vec+(*p16)->x2)*(*p16)->p;
//                    *p13+=*p11;
                }
                
                if(*p13+8*MACHINE_EPSILON<x_current)printf("Unexpected, not monotone increasing: node[%u]: x_current: %.17e difference: %.3e.\n",*p7,x_current,(x_current-*p13)/MACHINE_EPSILON);
                
//                if(*p13<x_current)*p13=x_current;
                
                err_current=fabs(*p13-x_current);
                if(err_current>err_max)err_max=err_current;
            }
            if(i==1)printf("Error_max after shift = %.17e.\t",err_max);
            if(err_max<=EPSILON)break;
            
        }
        printf("%u th iteration: ",j);
        if(i<=ITERATION_BOUND)printf("# of iterations: %u.",i);
        else printf("# of iterations exceeds ITERATION_BOUND %u.",ITERATION_BOUND);
        printf("\t err_max = %.17e.\n",err_max);
        cnt3+=i;
        if(i>ITERATION_BOUND)--cnt3;
        for(p14=sort_x,p15=p14+l2,p11=*p14,++p14;p14!=p15;++p14)
        {
            p12=*p14;
//            if(*p11<=*p12+MACHINE_EPSILON)p11=p12;
            if(*p11<=*p12)p11=p12;
            else break;
        }
        printf("\t%u\n",(uint32_t)(p14-sort_x));
        if(p14==p15)
        {
            if(i>ITERATION_BOUND){printf("Order doesn't change but needs more iterations.\n");continue;}
            else break;
        }
        qsort(sort_x,l2,sizeof(double*),cmp1);
        for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
            *(*p14-x_vec+permutation)=cnt2;
        // assign probability to edges
        p16=p17=sort_edge;
        for(p7=decode_max;p7!=p8;++p7)
        {
            p2=*(out_pos+*p7);
            if(!p2)continue;
            if(p2->p_u==0.0)
            {p16=p17+=p2->num;continue;}
            for(p18=p17+p2->num,p3=*p17,++p17;p17!=p18;++p17)
            {
                p4=*p17;
                if(*(permutation+p3->x2)<*(permutation+p4->x2))p3=p4;
                else break;
            }
            if(p17==p18){p16=p18;continue;}
            else p17=p18;
            qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
            for(p_tmp1=p2->p_u,err2=p2->p_l,tag=0;p16!=p17;++p16)
            {
                p4=*p16;
                if(tag)p4->p=p4->p_u;
                else
                {
                    p_tmp=p_tmp1;err1=err2;
                    sum_p(&p_tmp1,&err2,p4->p_l);
                    if(p_tmp1>p4->p_u)
                    {
                        p4->p=p4->p_l;
                        sum_m(&p_tmp1,&err2,p4->p_u);
                    }
                    else
                    {
                        p4->p=p4->p_u;err2=0;
                        sum_m(&p4->p,&err2,p_tmp);
                        sum_m(&p4->p,&err2,err1);
                        tag=2;
                    }
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p>p_tmp)
//                    {
//                        p4->p=p4->p_l;
//                        p2->p-=p_tmp;
//                    }
//                    else{p4->p=p4->p_u-p2->p;tag=2;}
                }
            }
            if(p2->x2)
            {p4=p2+p2->x2;p4->p=1.0/(1-p4->p);}
        }
    }
    
    printf("# of outer loop iterations :%u\n",j);
    printf("# of total loop iterations :%u\n",cnt3);

    for(p11=b_vec,p12=p11+l2,p13=x_vec;p11!=p12;++p11,++p13)
        *p11=*p13;
    head->x_vec_Gauss_Seidel_max=b_vec;
    imc->b_vec=0;
    free(x_vec);imc->x_vec=0;
    free(sort_edge);imc->sort_edge=0;
    
//    free(out_pos);imc->out_pos=0;
//    free(imc->out_edge);imc->out_edge=0;
//    free(decode1);head->decode1=0;
//    free(b_vec);imc->b_vec=0;
    end_t=clock();
    printf("Time used to solve (I-D-L)x = Ux + b = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("Time used to solve quantitative maximum reachability using Gauss Seidel method = %.4f\n",
           (double)(end_t-start_t0)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void solve_quantitative_max_reachability_power_GS_method(HEAD *head)
{
    IMC *imc;
    uint32_t n0,l2,cnt2,cnt3;
    uint32_t i,j;
    uint64_t cnt1;
    OUT_EDGE **out_pos,**sort_edge,*p2,*p3,*p4,**p16,**p17,**p18;
    uint32_t *encode_max,*decode_max,*p5,*p6,*p7,*p8;
    double err1,err2,p_tmp,p_tmp1,*x_vec,*b_vec,*p11,*p12,*p13,*x_current,*x_next,*x_tmp,x_crt,err_current,err_max = 0.0,err_max1=1.0,max_rel_err = 0.0,**sort_x,**p14,**p15;
    BOOL *flag,*p9,tag;
    clock_t start_t0,start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    out_pos=imc->out_pos;
    flag=head->flag_max;
    n0=imc->n;
    l2=head->l2_max;
    
    printf("Solve quantitative maximum reachability using power-GS method:\n");
    
    // MARK: build data structure for iterative method
    start_t0=start_t=clock();
    printf("Build data structure for iterative method:\n");
    if(!l2)
    {
        printf("All states have trivial probability 0 or 1, so no quantitative maximum reachability needs to be solved.\n");
        return;
    }
    // Encode and decode
    if(head->encode_max)
    {
        encode_max=head->encode_max;
        decode_max=head->decode_max;
        p8=decode_max+l2;
    }
    else
    {
        head->encode_max=encode_max=imc->queue;imc->queue=0;
        head->decode_max=decode_max=(uint32_t*)malloc(l2*sizeof(uint32_t));
        p5=encode_max;p7=decode_max;p9=flag;
        for(p6=p5+n0;p5!=p6;++p5,++p9)
            if(*p9==2)
            {
                *p5=(uint32_t)(p7-decode_max);
                *p7=(uint32_t)(p5-encode_max);++p7;
            }
            else *p5=n0;
    }
    // Compute sum_l and sum_u
    for(p7=decode_max,p8=p7+l2;p7!=p8;++p7)
    {
        p2=p4=*(out_pos+*p7);
        for(p2->p=p2->p_l=p2->p_u=err1=err2=0.0;p4->next;)
        {
            p4+=p4->next;
            sum_p(&p2->p_l,&err1,p4->p_l);
            sum_p(&p2->p_u,&err2,p4->p_u);
//            p2->p_l+=p4->p_l;
//            p2->p_u+=p4->p_u;
        }
        // Sterbenz's lemma
        if(1.0<=p2->p_l*2)p2->p_l=(1.0-p2->p_l)-err1;
        else
        {
            p_tmp=p2->p_l;p_tmp1=0.0;p2->p_l=1.0;
            sum_m(&p2->p_l,&p_tmp1,p_tmp);
            sum_m(&p2->p_l,&p_tmp1,err1);
        }
        sum_m(&p2->p_u,&err2,1.0);
        sum_p(&p2->p_u,&p2->p,err2);
//        p2->p_l=1.0-p2->p_l;p2->p_u-=1.0;
    }
    // Set up (I-D-L)x = Ux + b
    p11=imc->b_vec=b_vec=(double*)calloc(l2,sizeof(double));
    for(p7=decode_max,cnt1=0;p7!=p8;++p7,++p11)
    {
        p2=p3=p4=*(out_pos+*p7);
        err2=p2->p;
        err1=p2->p=0.0;
        for(p2->x2=p2->num=tag=0;p4->next;)
        {
            p4+=p4->next;
            p9=flag+p4->x2;
            if(*p9==2)
            {
                p3=p4;++p2->num;
                if(*p7==p4->x2)p2->x2=(uint32_t)(p4-p2);
                p4->x2=*(encode_max+p4->x2);
            }
            else
            {
                p3->next+=p4->next;
                if(*p9&1)// label == 1 || 3
                {
                    switch(tag)
                    {
                        case 0:
                        {
                            sum_p(&p2->p_l,&err1,p4->p_l);
                            if(p2->p_l>p4->p_u)
                            {
                                sum_p(p11,&p2->p,p4->p_u);
                                sum_m(&p2->p_l,&err1,p4->p_u);
                            }
                            else
                            {
                                sum_p(p11,&p2->p,p2->p_l);
                                sum_p(p11,&p2->p,err1);
                                tag=1;
                            }
//                            p_tmp=p4->p_u-p4->p_l;
//                            if(p2->p_l>p_tmp)
//                            {
//                                *p11+=p4->p_u;
//                                p2->p_l-=p_tmp;
//                            }
//                            else
//                            {*p11+=p4->p_l+p2->p_l;tag=1;}
                        }
                        break;
                        case 1:
                        sum_p(p11,&p2->p,p4->p_l);
//                        *p11+=p4->p_l;
                        break;
                        case 2:
                        sum_p(p11,&p2->p,p4->p_u);
//                        *p11+=p4->p_u;
                    }
                }
                else if(!tag)
                {
                    sum_p(&p2->p_u,&err2,p4->p_l);
                    if(p2->p_u>p4->p_u)
                    sum_m(&p2->p_u,&err2,p4->p_u);
                    else tag=2;
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p_u>p_tmp)
//                    {p2->p_u-=p_tmp;}
//                    else{tag=2;}
                }
            }
        }
        if(p3!=p2)p3->next=0;else p2=0;
        if(!p2)continue;
        cnt1+=p2->num;
        if(tag)
        {
            p2->p_u=0.0;
            if(tag&1)
            {
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_l;}
                if(p2->x2)
                {p4=p2+p2->x2;p4->p=1.0/(1-p4->p_l);}
            }
            else
            {
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_u;}
                if(p2->x2)
                {p4=p2+p2->x2;p4->p=1.0/(1-p4->p_u);}
            }
        }else{p2->p_l=err2;}
    }
    printf("Size of iteration matrix = n + m = %u + %llu = %llu.\n",l2,cnt1,l2+cnt1);
    printf("Size of sort_edge = %llu.\n",cnt1);
    imc->x_vec=x_vec=(double*)malloc((l2<<1)*sizeof(double));//l2*2
    if(imc->sort_x)sort_x=imc->sort_x;
    else
    {
        imc->sort_x=sort_x=(double**)malloc(l2*sizeof(double*));
    }
    // x(0)=0, x(1)=b(for sort)
    p11=b_vec;p12=p11+l2;p13=x_vec;p14=sort_x;
    for(;p11!=p12;++p11,++p13,++p14)
    {*p13=*p11;*p14=p13;}
    // Sort x(1)
    qsort(sort_x,l2,sizeof(double*),cmp1);
    if(!permutation)
    permutation=(uint32_t*)malloc(l2*sizeof(uint32_t));
    for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
        *(*p14-x_vec+permutation)=cnt2;
    
    p16=p17=imc->sort_edge=sort_edge=(OUT_EDGE**)malloc(cnt1*sizeof(OUT_EDGE*));
    // assign probability to edges, x(1)=(I-D)^{-1}b <= (I-D-L)^{-1}b
    for(p7=decode_max,p13=x_vec;p7!=p8;++p7,++p13)
    {
        p2=p4=*(out_pos+*p7);
        if(!p2)continue;
        for(;p4->next;++p17)
        {p4+=p4->next;*p17=p4;}
        qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
        if(p2->p_u==0.0)
        {
            p16=p17;
            if(p2->x2)
            {
                p4=p2+p2->x2;*p13*=p4->p;
                err2=p2->p*p4->p;*p13+=err2;
            }
            continue;
        }
        for(p_tmp1=p2->p_u,err2=p2->p_l,tag=0;p16!=p17;++p16)
        {
            p4=*p16;
            if(tag)p4->p=p4->p_u;
            else
            {
                p_tmp=p_tmp1;err1=err2;
                sum_p(&p_tmp1,&err2,p4->p_l);
                if(p_tmp1>p4->p_u)
                {
                    p4->p=p4->p_l;
                    sum_m(&p_tmp1,&err2,p4->p_u);
                }
                else
                {
                    p4->p=p4->p_u;err2=0;
                    sum_m(&p4->p,&err2,p_tmp);
                    sum_m(&p4->p,&err2,err1);
                    tag=2;
                }
//                p_tmp=p4->p_u-p4->p_l;
//                if(p2->p>p_tmp)
//                {
//                    p4->p=p4->p_l;
//                    p2->p-=p_tmp;
//                }
//                else{p4->p=p4->p_u-p2->p;tag=2;}
            }
        }
        if(p2->x2)
        {
            p4=p2+p2->x2;
            p4->p=1.0/(1-p4->p);
            *p13*=p4->p;
            err2=p2->p*p4->p;*p13+=err2;
        }
    }
    end_t=clock();
    printf("Time used to build data structure for iterative method = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    
    // MARK: Solve (I-D-L)x = Ux + b
    start_t=clock();
    printf("Solve (I-D-L)x = Ux + b:\n");
    for(cnt3=0,j=1;;++j)
    {
        for(i=1;i<=ITERATION_BOUND1;++i)
        {
            p7=decode_max;p11=b_vec;
            p16=p17=sort_edge;
            p13=x_vec;
            err_max=0.0;
            for(;p7!=p8;++p7,++p11,++p12,++p13)
            {
                x_crt=*p13;
                p2=p4=*(out_pos+*p7);
                if(!p4){*p13=*p11;continue;}
                if(p2->x2)
                {
                    p3=p2+p2->x2;
                    *p13=p4->p;err2=0.0;p17=p16+p4->num;
                    for(;p16!=p17;++p16)
                        if(*p16!=p3)
                        {
                            p_tmp=*(x_vec+(*p16)->x2)*(*p16)->p;
                            sum_p(p13,&err2,p_tmp);
                        }
                    sum_p(p13,&err2,*p11);
                    *p13*=p3->p;err2*=p3->p;*p13+=err2;
                    
//                    p3=p2+p2->x2;
//                    *p13=0;p17=p16+p4->num;
//                    for(;p16!=p17;++p16)
//                        if(*p16!=p3)*p13+=*(x_vec+(*p16)->x2)*(*p16)->p;
//                    *p13+=*p11;*p13*=p3->p;
                }
                else
                {
                    *p13=p4->p;err2=0.0;p17=p16+p4->num;
                    for(;p16!=p17;++p16)
                    {
                        p_tmp=*(x_vec+(*p16)->x2)*(*p16)->p;
                        sum_p(p13,&err2,p_tmp);
                    }
                    sum_p(p13,&err2,*p11);
                    
//                    *p13=0;p17=p16+p4->num;
//                    for(;p16!=p17;++p16)
//                    *p13+=*(x_vec+(*p16)->x2)*(*p16)->p;
//                    *p13+=*p11;
                }
                
                if(*p13+4*MACHINE_EPSILON<x_crt)printf("Unexpected, not monotone increasing: node[%u]: x_current: %.17e difference: %.3e.\n",*p7,x_crt,(x_crt-*p13)/MACHINE_EPSILON);
                if (*p13>1)*p13=1;
//                if(*p13<x_crt)*p13=x_crt;
                
                err_current=fabs(*p13-x_crt);
                if(err_current>err_max)err_max=err_current;
            }
            if(i==1)printf("Error_max after shift = %.17e.\t",err_max);
            if(err_max<=EPSILON1)break;
            
        }
        printf("%u th iteration: ",j);
        if(i<=ITERATION_BOUND1)printf("# of iterations: %u.",i);
        else printf("# of iterations exceeds ITERATION_BOUND %u.",ITERATION_BOUND1);
        printf("\t err_max = %.17e.\n",err_max);
        cnt3+=i;
        if(i>ITERATION_BOUND1)--cnt3;
        for(p14=sort_x,p15=p14+l2,p11=*p14,++p14;p14!=p15;++p14)
        {
            p12=*p14;
//            if(*p11<=*p12+MACHINE_EPSILON)p11=p12;
            if(*p11<=*p12)p11=p12;
            else break;
        }
        printf("\t%u\n",(uint32_t)(p14-sort_x));
        if(p14==p15)
        {
            if(i>ITERATION_BOUND1){printf("Order doesn't change but needs more iterations.\n");continue;}
            else break;
        }
        if(err_max<=EPSILON1)break;
        qsort(sort_x,l2,sizeof(double*),cmp1);
        for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
            *(*p14-x_vec+permutation)=cnt2;
        // assign probability to edges
        p16=p17=sort_edge;
        for(p7=decode_max;p7!=p8;++p7)
        {
            p2=*(out_pos+*p7);
            if(!p2)continue;
            if(p2->p_u==0.0)
            {p16=p17+=p2->num;continue;}
            for(p18=p17+p2->num,p3=*p17,++p17;p17!=p18;++p17)
            {
                p4=*p17;
                if(*(permutation+p3->x2)<*(permutation+p4->x2))p3=p4;
                else break;
            }
            if(p17==p18){p16=p18;continue;}
            else p17=p18;
            qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
            for(p_tmp1=p2->p_u,err2=p2->p_l,tag=0;p16!=p17;++p16)
            {
                p4=*p16;
                if(tag)p4->p=p4->p_u;
                else
                {
                    p_tmp=p_tmp1;err1=err2;
                    sum_p(&p_tmp1,&err2,p4->p_l);
                    if(p_tmp1>p4->p_u)
                    {
                        p4->p=p4->p_l;
                        sum_m(&p_tmp1,&err2,p4->p_u);
                    }
                    else
                    {
                        p4->p=p4->p_u;err2=0;
                        sum_m(&p4->p,&err2,p_tmp);
                        sum_m(&p4->p,&err2,err1);
                        tag=2;
                    }
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p>p_tmp)
//                    {
//                        p4->p=p4->p_l;
//                        p2->p-=p_tmp;
//                    }
//                    else{p4->p=p4->p_u-p2->p;tag=2;}
                }
            }
            if(p2->x2)
            {p4=p2+p2->x2;p4->p=1.0/(1-p4->p);}
        }
    }
    
    printf("# of outer loop iterations :%u\n",j);
    printf("# of total loop iterations :%u\n",cnt3);
    
    end_t=clock();
    printf("Time used to solve (I-D-L)x = Ux + b = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    
    // MARK: Solve x = Ax + b
    start_t=clock();
    printf("Solve x = Ax + b:\n");
    qsort(sort_x,l2,sizeof(double*),cmp1);
    for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
        *(*p14-x_vec+permutation)=cnt2;
    // assign probability to edges
    p16=p17=sort_edge;
    for(p7=decode_max;p7!=p8;++p7)
    {
        p2=*(out_pos+*p7);
        if(!p2)continue;
        if(p2->p_u==0.0)
        {
            p16=p17+=p2->num;
            if(p2->x2)
            {
                p4=p2+p2->x2;
                if(p4->p==1.0/(1-p4->p_l))p4->p=p4->p_l;
                else if(p4->p==1.0/(1-p4->p_u))p4->p=p4->p_u;
                else printf("Bug in 1.0/(1-p).\n");
            }
            continue;
        }
        p17=p16+p2->num;
        qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
        for(p_tmp1=p2->p_u,err2=p2->p_l,tag=0;p16!=p17;++p16)
        {
            p4=*p16;
            if(tag)p4->p=p4->p_u;
            else
            {
                p_tmp=p_tmp1;err1=err2;
                sum_p(&p_tmp1,&err2,p4->p_l);
                if(p_tmp1>p4->p_u)
                {
                    p4->p=p4->p_l;
                    sum_m(&p_tmp1,&err2,p4->p_u);
                }
                else
                {
                    p4->p=p4->p_u;err2=0;
                    sum_m(&p4->p,&err2,p_tmp);
                    sum_m(&p4->p,&err2,err1);
                    tag=2;
                }
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p>p_tmp)
//                    {
//                        p4->p=p4->p_l;
//                        p2->p-=p_tmp;
//                    }
//                    else{p4->p=p4->p_u-p2->p;tag=2;}
            }
        }
    }
    x_current=x_vec;x_next=x_vec+l2;
    for(cnt3=0,j=1;;++j)
    {
        for(i=1;i<=ITERATION_BOUND2;++i)
        {
            p7=decode_max;p11=b_vec;
            p16=p17=sort_edge;
            p12=x_current;p13=x_next;
            err_max=0.0;max_rel_err=0.0;cnt2=0;
            for(;p7!=p8;++p7,++p11,++p12,++p13)
            {
                p4=*(out_pos+*p7);
                if(!p4){*p13=*p11;continue;}
                for(*p13=p4->p,err2=0.0,p17=p16+p4->num;p16!=p17;++p16)
                {
                    p_tmp=*(x_current+(*p16)->x2)*(*p16)->p;
                    sum_p(p13,&err2,p_tmp);
                }
                sum_p(p13,&err2,*p11);
                p_tmp=*p13*EPS;
                sum_p(p13,&err2,p_tmp);
//                for(*p13=0,p17=p16+p4->num;p16!=p17;++p16)
//                    *p13+=*(x_current+(*p16)->x2)*(*p16)->p;
//                *p13+=*p11;
                
                if(*p13+*p13*MACHINE_EPSILON<*p12)printf("Unexpected, not monotone increasing: node[%u]: x_current: %.17e difference: %.3e.\n",*p7,*p12,(*p12-*p13)/MACHINE_EPSILON);
                
                if(*p13<*p12)++cnt2;
                
//                if(*p13<*p12)*p13=*p12;
                
                err_current=fabs(*p13-*p12);
                if(err_current>err_max)err_max=err_current;
                if(err_current!=0.0)
                {
                    p_tmp=err_current/(__DBL_EPSILON__**p13);
                    if(p_tmp>max_rel_err)max_rel_err=p_tmp;
                }
            }
            if(cnt2)
            printf("# not monotone: %u\t",cnt2);
            //swap x_current and x_next
            x_tmp=x_current;
            x_current=x_next;
            x_next=x_tmp;
            if(i==1)
            {
                printf("Error_max after shift = %.17e.\t",err_max);
                printf("# not monotone: %u\t",cnt2);
            }
            if(err_max1<err_max)printf("Inner # %u: relative error violation: %.17e, current error: %.17e, previous error: %.17e.\n",i,(err_max-err_max1)/err_max,err_max,err_max1);
            err_max1=err_max;
            
            if(err_max<=EPSILON2)break;
//            printf("max_rel_err = %.17e.\n",max_rel_err);
            if(max_rel_err<REL_ERR_THRES)break;
        }
        printf("max_rel_err = %.17e.\n",max_rel_err);
        printf("%u th iteration: ",j);
        if(i<=ITERATION_BOUND2)printf("# of iterations: %u.",i);
        else printf("# of iterations exceeds ITERATION_BOUND %u.",ITERATION_BOUND2);
        printf("\t err_max = %.17e.",err_max);
        cnt3+=i;
        if(i>ITERATION_BOUND2)--cnt3;
        for(p14=sort_x,p15=p14+l2,p11=*p14,++p14;p14!=p15;++p14)
        {
            p12=*p14;
            if(*p11<=*p12)p11=p12;
            else break;
        }
        printf("\t%u\n",(uint32_t)(p14-sort_x));
        if(p14==p15)
        {
            if(i>ITERATION_BOUND2){printf("Order doesn't change but needs more iterations.\n");continue;}
            else break;
        }
        
        qsort(sort_x,l2,sizeof(double*),cmp1);
        for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
            *(*p14-x_vec+permutation)=cnt2;
        // assign probability to edges
        p16=p17=sort_edge;
        for(p7=decode_max;p7!=p8;++p7)
        {
            p2=*(out_pos+*p7);
            if(!p2)continue;
            if(p2->p_u==0.0)
            {p16=p17+=p2->num;continue;}
            for(p18=p17+p2->num,p3=*p17,++p17;p17!=p18;++p17)
            {
                p4=*p17;
                if(*(permutation+p3->x2)<*(permutation+p4->x2))p3=p4;
                else break;
            }
            if(p17==p18){p16=p18;continue;}
            else p17=p18;
            qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
            for(p_tmp1=p2->p_u,err2=p2->p_l,tag=0;p16!=p17;++p16)
            {
                p4=*p16;
                if(tag)p4->p=p4->p_u;
                else
                {
                    p_tmp=p_tmp1;err1=err2;
                    sum_p(&p_tmp1,&err2,p4->p_l);
                    if(p_tmp1>p4->p_u)
                    {
                        p4->p=p4->p_l;
                        sum_m(&p_tmp1,&err2,p4->p_u);
                    }
                    else
                    {
                        p4->p=p4->p_u;err2=0;
                        sum_m(&p4->p,&err2,p_tmp);
                        sum_m(&p4->p,&err2,err1);
                        tag=2;
                    }
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p>p_tmp)
//                    {
//                        p4->p=p4->p_l;
//                        p2->p-=p_tmp;
//                    }
//                    else{p4->p=p4->p_u-p2->p;tag=2;}
                }
            }
        }
    }
    
    printf("# of outer loop iterations :%u\n",j);
    printf("# of total loop iterations :%u\n",cnt3);
    
    for(p11=b_vec,p12=p11+l2,p13=x_current;p11!=p12;++p11,++p13)
        *p11=*p13;
    head->x_vec_power_max=b_vec;
    imc->b_vec=0;
    free(x_vec);imc->x_vec=0;
    free(sort_edge);imc->sort_edge=0;
    
//    free(out_pos);imc->out_pos=0;
//    free(imc->out_edge);imc->out_edge=0;
//    free(decode1);head->decode1=0;
//    free(b_vec);imc->b_vec=0;
    
    end_t=clock();
    printf("Time used to solve x = Ax + b = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("Time used to solve quantitative maximum reachability using power-GS method = %.4f\n",
           (double)(end_t-start_t0)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void solve_quantitative_max_reachability_power_method_modified(HEAD *head)
{
    IMC *imc;
    uint32_t n0,l2,cnt2,cnt3;
    uint32_t i,j;
    uint64_t cnt1;
    OUT_EDGE **out_pos,**sort_edge,*p2,*p3,*p4,**p16,**p17,**p18;
    uint32_t *encode_max,*decode_max,*p5,*p6,*p7,*p8;
    double err1,err2,p_tmp,p_tmp1,*x_vec,*b_vec,*p11,*p12,*p13,*x_current,*x_next,*x_tmp,err_current,err_max = 0.0,err_max1=1.0,max_rel_err = 0.0,**sort_x,**p14,**p15;
    BOOL *flag,*p9,tag;
    clock_t start_t0,start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    out_pos=imc->out_pos;
    flag=head->flag_max;
    n0=imc->n;
    l2=head->l2_max;
    
    printf("Solve quantitative maximum reachability using power method:\n");
    
    // MARK: build data structure for iterative method
    start_t0=start_t=clock();
    printf("Build data structure for iterative method:\n");
    if(!l2)
    {
        printf("All states have trivial probability 0 or 1, so no quantitative maximum reachability needs to be solved.\n");
        return;
    }
    // Encode and decode
    if(head->encode_max)
    {
        encode_max=head->encode_max;
        decode_max=head->decode_max;
        p8=decode_max+l2;
    }
    else
    {
        head->encode_max=encode_max=imc->queue;imc->queue=0;
        head->decode_max=decode_max=(uint32_t*)malloc(l2*sizeof(uint32_t));
        p5=encode_max;p7=decode_max;p9=flag;
        for(p6=p5+n0;p5!=p6;++p5,++p9)
            if(*p9==2)
            {
                *p5=(uint32_t)(p7-decode_max);
                *p7=(uint32_t)(p5-encode_max);++p7;
            }
            else *p5=n0;
    }
    // Compute sum_l and sum_u
    for(p7=decode_max,p8=p7+l2;p7!=p8;++p7)
    {
        p2=p4=*(out_pos+*p7);
        for(p2->p=p2->p_l=p2->p_u=err1=err2=0.0;p4->next;)
        {
            p4+=p4->next;
            sum_p(&p2->p_l,&err1,p4->p_l);
            sum_p(&p2->p_u,&err2,p4->p_u);
//            p2->p_l+=p4->p_l;
//            p2->p_u+=p4->p_u;
        }
        // Sterbenz's lemma
        if(1.0<=p2->p_l*2)p2->p_l=(1.0-p2->p_l)-err1;
        else
        {
            p_tmp=p2->p_l;p_tmp1=0.0;p2->p_l=1.0;
            sum_m(&p2->p_l,&p_tmp1,p_tmp);
            sum_m(&p2->p_l,&p_tmp1,err1);
        }
        sum_m(&p2->p_u,&err2,1.0);
        sum_p(&p2->p_u,&p2->p,err2);
//        p2->p_l=1.0-p2->p_l;p2->p_u-=1.0;
    }
    // Set up x = Ax + b
    p11=imc->b_vec=b_vec=(double*)calloc(l2,sizeof(double));
    for(p7=decode_max,cnt1=0;p7!=p8;++p7,++p11)
    {
        p2=p3=p4=*(out_pos+*p7);
        err2=p2->p;
        err1=p2->p=0.0;
        for(p2->num=tag=0;p4->next;)
        {
            p4+=p4->next;
            p9=flag+p4->x2;
            if(*p9==2)
            {p3=p4;++p2->num;p4->x2=*(encode_max+p4->x2);}
            else
            {
                p3->next+=p4->next;
                if(*p9&1)// label == 1 || 3
                {
                    switch(tag)
                    {
                        case 0:
                        {
                            sum_p(&p2->p_l,&err1,p4->p_l);
                            if(p2->p_l>p4->p_u)
                            {
                                sum_p(p11,&p2->p,p4->p_u);
                                sum_m(&p2->p_l,&err1,p4->p_u);
                            }
                            else
                            {
                                sum_p(p11,&p2->p,p2->p_l);
                                sum_p(p11,&p2->p,err1);
                                tag=1;
                            }
//                            p_tmp=p4->p_u-p4->p_l;
//                            if(p2->p_l>p_tmp)
//                            {
//                                *p11+=p4->p_u;
//                                p2->p_l-=p_tmp;
//                            }
//                            else
//                            {*p11+=p4->p_l+p2->p_l;tag=1;}
                        }
                        break;
                        case 1:
                        sum_p(p11,&p2->p,p4->p_l);
//                        *p11+=p4->p_l;
                        break;
                        case 2:
                        sum_p(p11,&p2->p,p4->p_u);
//                        *p11+=p4->p_u;
                    }
                }
                else if(!tag)
                {
                    sum_p(&p2->p_u,&err2,p4->p_l);
                    if(p2->p_u>p4->p_u)
                    sum_m(&p2->p_u,&err2,p4->p_u);
                    else tag=2;
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p_u>p_tmp)
//                    {p2->p_u-=p_tmp;}
//                    else{tag=2;}
                }
            }
        }
        if(p3!=p2)p3->next=0;else p2=0;
        if(!p2)continue;
        cnt1+=p2->num;
        if(tag)
        {
            p2->p_u=0.0;
            if(tag&1)
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_l;}
            else
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_u;}
        }else{p2->p_l=err2;}
    }
    printf("Size of iteration matrix = n + m = %u + %llu = %llu.\n",l2,cnt1,l2+cnt1);
    printf("Size of sort_edge = %llu.\n",cnt1);
    imc->x_vec=x_vec=(double*)malloc((l2<<1)*sizeof(double));//l2*2
    if(imc->sort_x)sort_x=imc->sort_x;
    else
    {
        imc->sort_x=sort_x=(double**)malloc(l2*sizeof(double*));
    }
    // x(0)=0, x(1)=b
    p11=b_vec;p12=p11+l2;p13=x_vec;p14=sort_x;
    for(;p11!=p12;++p11,++p13,++p14)
    {*p13=*p11;*p14=p13;}
    x_current=x_vec;x_next=x_vec+l2;
    // Sort x(1)
    qsort(sort_x,l2,sizeof(double*),cmp1);
    if(!permutation)
    permutation=(uint32_t*)malloc(l2*sizeof(uint32_t));
    for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
        *(*p14-x_vec+permutation)=cnt2;
    
    p16=p17=imc->sort_edge=sort_edge=(OUT_EDGE**)malloc(cnt1*sizeof(OUT_EDGE*));
    // assign probability to edges
    for(p7=decode_max;p7!=p8;++p7)
    {
        p2=p4=*(out_pos+*p7);
        if(!p2)continue;
        for(;p4->next;++p17)
        {p4+=p4->next;*p17=p4;}
        qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
        if(p2->p_u==0.0){p16=p17;continue;}
        for(p_tmp1=p2->p_u,err2=p2->p_l,tag=0;p16!=p17;++p16)
        {
            p4=*p16;
            if(tag)p4->p=p4->p_u;
            else
            {
                p_tmp=p_tmp1;err1=err2;
                sum_p(&p_tmp1,&err2,p4->p_l);
                if(p_tmp1>p4->p_u)
                {
                    p4->p=p4->p_l;
                    sum_m(&p_tmp1,&err2,p4->p_u);
                }
                else
                {
                    p4->p=p4->p_u;err2=0;
                    sum_m(&p4->p,&err2,p_tmp);
                    sum_m(&p4->p,&err2,err1);
                    tag=2;
                }
//                p_tmp=p4->p_u-p4->p_l;
//                if(p2->p>p_tmp)
//                {
//                    p4->p=p4->p_l;
//                    p2->p-=p_tmp;
//                }
//                else{p4->p=p4->p_u-p2->p;tag=2;}
            }
        }
    }
    end_t=clock();
    printf("Time used to build data structure for iterative method = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    
    // MARK: Solve x = Ax + b
    start_t=clock();
    printf("Solve x = Ax + b:\n");
    for(cnt3=0,j=1;;++j)
    {
        for(i=1;i<=ITERATION_BOUND;++i)
        {
            p7=decode_max;p11=b_vec;
            p16=p17=sort_edge;
            p12=x_current;p13=x_next;
            err_max=0.0;max_rel_err=0.0;cnt2=0;
            for(;p7!=p8;++p7,++p11,++p12,++p13)
            {
                p4=*(out_pos+*p7);
                if(!p4){*p13=*p11;continue;}
                for(*p13=p4->p,err2=0.0,p17=p16+p4->num;p16!=p17;++p16)
                {
                    p_tmp=*(x_current+(*p16)->x2)*(*p16)->p;
                    sum_p(p13,&err2,p_tmp);
                }
                sum_p(p13,&err2,*p11);
                
                p_tmp=*p13*EPS;
                sum_p(p13,&err2,p_tmp);
                
                
//                for(*p13=0,p17=p16+p4->num;p16!=p17;++p16)
//                    *p13+=*(x_current+(*p16)->x2)*(*p16)->p;
//                *p13+=*p11;
                
                
                if(*p13+*p13*MACHINE_EPSILON<*p12)printf("Unexpected, not monotone increasing: node[%u]: x_current: %.17e difference: %.3e.\n",*p7,*p12,(*p12-*p13)/MACHINE_EPSILON);
                
                if(*p13<*p12)++cnt2;
                
//                if(*p13<*p12)*p13=*p12;
                
                err_current=fabs(*p13-*p12);
                if(err_current>err_max)err_max=err_current;
                if(err_current!=0.0)
                {
                    p_tmp=err_current/(__DBL_EPSILON__**p13);
                    if(p_tmp>max_rel_err)max_rel_err=p_tmp;
                }
                
                
            }
            
            if(cnt2)
            printf("# not monotone: %u\t",cnt2);
            //swap x_current and x_next
            x_tmp=x_current;
            x_current=x_next;
            x_next=x_tmp;
            if(i==1)
            {
                printf("Error_max after shift = %.17e.\t",err_max);
                printf("# not monotone: %u\t",cnt2);
            }
            
            if(err_max1<err_max)printf("Inner # %u: relative error violation: %.17e, current error: %.17e, previous error: %.17e.\n",i,(err_max-err_max1)/err_max,err_max,err_max1);
            err_max1=err_max;
            
//            if(err_max<=EPSILON)break;
            
//            printf("max_rel_err = %.17e.\n",max_rel_err);
            if(max_rel_err<REL_ERR_THRES)break;
        }
        printf("max_rel_err = %.17e.\n",max_rel_err);
        printf("%u th iteration: ",j);
        if(i<=ITERATION_BOUND)printf("# of iterations: %u.",i);
        else printf("# of iterations exceeds ITERATION_BOUND %u.",ITERATION_BOUND);
        printf("\t err_max = %.17e.",err_max);
        cnt3+=i;
        if(i>ITERATION_BOUND)--cnt3;
        for(p14=sort_x,p15=p14+l2,p11=*p14,++p14;p14!=p15;++p14)
        {
            p12=*p14;
            if(*p11<=*p12)p11=p12;
            else break;
        }
        printf("\t%u\n",(uint32_t)(p14-sort_x));
        if(p14==p15)
        {
            if(i>ITERATION_BOUND){printf("Order doesn't change but needs more iterations.\n");continue;}
            else break;
        }
        
        qsort(sort_x,l2,sizeof(double*),cmp1);
        for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
            *(*p14-x_vec+permutation)=cnt2;
        // assign probability to edges
        p16=p17=sort_edge;
        for(p7=decode_max;p7!=p8;++p7)
        {
            p2=*(out_pos+*p7);
            if(!p2)continue;
            if(p2->p_u==0.0)
            {p16=p17+=p2->num;continue;}
            for(p18=p17+p2->num,p3=*p17,++p17;p17!=p18;++p17)
            {
                p4=*p17;
                if(*(permutation+p3->x2)<*(permutation+p4->x2))p3=p4;
                else break;
            }
            if(p17==p18){p16=p18;continue;}
            else p17=p18;
            qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
            for(p_tmp1=p2->p_u,err2=p2->p_l,tag=0;p16!=p17;++p16)
            {
                p4=*p16;
                if(tag)p4->p=p4->p_u;
                else
                {
                    p_tmp=p_tmp1;err1=err2;
                    sum_p(&p_tmp1,&err2,p4->p_l);
                    if(p_tmp1>p4->p_u)
                    {
                        p4->p=p4->p_l;
                        sum_m(&p_tmp1,&err2,p4->p_u);
                    }
                    else
                    {
                        p4->p=p4->p_u;err2=0;
                        sum_m(&p4->p,&err2,p_tmp);
                        sum_m(&p4->p,&err2,err1);
                        tag=2;
                    }
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p>p_tmp)
//                    {
//                        p4->p=p4->p_l;
//                        p2->p-=p_tmp;
//                    }
//                    else{p4->p=p4->p_u-p2->p;tag=2;}
                }
            }
        }
    }
    
    printf("# of outer loop iterations :%u\n",j);
    printf("# of total loop iterations :%u\n",cnt3);
    
    for(p11=b_vec,p12=p11+l2,p13=x_current;p11!=p12;++p11,++p13)
        *p11=*p13;
    head->x_vec_power_max=b_vec;
    imc->b_vec=0;
    free(x_vec);imc->x_vec=0;
    free(sort_edge);imc->sort_edge=0;
    
    
//    free(out_pos);imc->out_pos=0;
//    free(imc->out_edge);imc->out_edge=0;
//    free(decode1);head->decode1=0;
//    free(b_vec);imc->b_vec=0;
    end_t=clock();
    printf("Time used to solve x = Ax + b = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("Time used to solve quantitative maximum reachability using power method = %.4f\n",
           (double)(end_t-start_t0)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void solve_quantitative_max_reachability_power_method_aggressive(HEAD *head)
{
    IMC *imc;
    uint32_t n0,l2,cnt2,cnt3;
    uint32_t i,j;
    uint64_t cnt1;
    OUT_EDGE **out_pos,**sort_edge,*p2,*p3,*p4,**p16,**p17,**p18;
    uint32_t *encode_max,*decode_max,*p5,*p6,*p7,*p8;
    double err1,err2,p_tmp,p_tmp1,*x_vec,*b_vec,*p11,*p12,*p13,*x_current,*x_next,*x_tmp,err_current,err_max = 0.0,err_max1=1.0,max_rel_err = 0.0,**sort_x,**p14,**p15;
    BOOL *flag,*p9,tag;
    clock_t start_t0,start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    out_pos=imc->out_pos;
    flag=head->flag_max;
    n0=imc->n;
    l2=head->l2_max;
    
    printf("Solve quantitative maximum reachability using power method:\n");
    
    // MARK: build data structure for iterative method
    start_t0=start_t=clock();
    printf("Build data structure for iterative method:\n");
    if(!l2)
    {
        printf("All states have trivial probability 0 or 1, so no quantitative maximum reachability needs to be solved.\n");
        return;
    }
    // Encode and decode
    if(head->encode_max)
    {
        encode_max=head->encode_max;
        decode_max=head->decode_max;
        p8=decode_max+l2;
    }
    else
    {
        head->encode_max=encode_max=imc->queue;imc->queue=0;
        head->decode_max=decode_max=(uint32_t*)malloc(l2*sizeof(uint32_t));
        p5=encode_max;p7=decode_max;p9=flag;
        for(p6=p5+n0;p5!=p6;++p5,++p9)
            if(*p9==2)
            {
                *p5=(uint32_t)(p7-decode_max);
                *p7=(uint32_t)(p5-encode_max);++p7;
            }
            else *p5=n0;
    }
    // Compute sum_l and sum_u
    for(p7=decode_max,p8=p7+l2;p7!=p8;++p7)
    {
        p2=p4=*(out_pos+*p7);
        for(p2->p=p2->p_l=p2->p_u=err1=err2=0.0;p4->next;)
        {
            p4+=p4->next;
            sum_p(&p2->p_l,&err1,p4->p_l);
            sum_p(&p2->p_u,&err2,p4->p_u);
//            p2->p_l+=p4->p_l;
//            p2->p_u+=p4->p_u;
        }
        // Sterbenz's lemma
        if(1.0<=p2->p_l*2)p2->p_l=(1.0-p2->p_l)-err1;
        else
        {
            p_tmp=p2->p_l;p_tmp1=0.0;p2->p_l=1.0;
            sum_m(&p2->p_l,&p_tmp1,p_tmp);
            sum_m(&p2->p_l,&p_tmp1,err1);
        }
        sum_m(&p2->p_u,&err2,1.0);
        sum_p(&p2->p_u,&p2->p,err2);
//        p2->p_l=1.0-p2->p_l;p2->p_u-=1.0;
    }
    // Set up x = Ax + b
    p11=imc->b_vec=b_vec=(double*)calloc(l2,sizeof(double));
    for(p7=decode_max,cnt1=0;p7!=p8;++p7,++p11)
    {
        p2=p3=p4=*(out_pos+*p7);
        err2=p2->p;
        err1=p2->p=0.0;
        for(p2->num=tag=0,p2->x2=1<<4;p4->next;)
        {
            p4+=p4->next;
            p9=flag+p4->x2;
            if(*p9==2)
            {p3=p4;++p2->num;p4->x2=*(encode_max+p4->x2);}
            else
            {
                p3->next+=p4->next;
                if(*p9&1)// label == 1 || 3
                {
                    switch(tag)
                    {
                        case 0:
                        {
                            sum_p(&p2->p_l,&err1,p4->p_l);
                            if(p2->p_l>p4->p_u)
                            {
                                sum_p(p11,&p2->p,p4->p_u);
                                sum_m(&p2->p_l,&err1,p4->p_u);
                            }
                            else
                            {
                                sum_p(p11,&p2->p,p2->p_l);
                                sum_p(p11,&p2->p,err1);
                                tag=1;
                            }
//                            p_tmp=p4->p_u-p4->p_l;
//                            if(p2->p_l>p_tmp)
//                            {
//                                *p11+=p4->p_u;
//                                p2->p_l-=p_tmp;
//                            }
//                            else
//                            {*p11+=p4->p_l+p2->p_l;tag=1;}
                        }
                        break;
                        case 1:
                        sum_p(p11,&p2->p,p4->p_l);
//                        *p11+=p4->p_l;
                        break;
                        case 2:
                        sum_p(p11,&p2->p,p4->p_u);
//                        *p11+=p4->p_u;
                    }
                }
                else if(!tag)
                {
                    sum_p(&p2->p_u,&err2,p4->p_l);
                    if(p2->p_u>p4->p_u)
                    sum_m(&p2->p_u,&err2,p4->p_u);
                    else tag=2;
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p_u>p_tmp)
//                    {p2->p_u-=p_tmp;}
//                    else{tag=2;}
                }
            }
        }
        if(p3!=p2)p3->next=0;else p2=0;
        if(!p2)continue;
        cnt1+=p2->num;
        if(tag)
        {
            p2->p_u=0.0;
            if(tag&1)
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_l;}
            else
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_u;}
        }else{p2->p_l=err2;}
    }
    printf("Size of iteration matrix = n + m = %u + %llu = %llu.\n",l2,cnt1,l2+cnt1);
    printf("Size of sort_edge = %llu.\n",cnt1);
    imc->x_vec=x_vec=(double*)malloc((l2<<1)*sizeof(double));//l2*2
    if(imc->sort_x)sort_x=imc->sort_x;
    else
    {
        imc->sort_x=sort_x=(double**)malloc(l2*sizeof(double*));
    }
    // x(0)=0, x(1)=b
    p11=b_vec;p12=p11+l2;p13=x_vec;p14=sort_x;
    for(;p11!=p12;++p11,++p13,++p14)
    {*p13=*p11+MACHINE_EPSILON;*p14=p13;}
    x_current=x_vec;x_next=x_vec+l2;
    // Sort x(1)
    qsort(sort_x,l2,sizeof(double*),cmp1);
    if(!permutation)
    permutation=(uint32_t*)malloc(l2*sizeof(uint32_t));
    for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
        *(*p14-x_vec+permutation)=cnt2;
    
    p16=p17=imc->sort_edge=sort_edge=(OUT_EDGE**)malloc(cnt1*sizeof(OUT_EDGE*));
    // assign probability to edges
    for(p7=decode_max;p7!=p8;++p7)
    {
        p2=p4=*(out_pos+*p7);
        if(!p2)continue;
        for(;p4->next;++p17)
        {p4+=p4->next;*p17=p4;}
        qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
        if(p2->p_u==0.0){p16=p17;continue;}
        for(p_tmp1=p2->p_u,err2=p2->p_l,tag=0;p16!=p17;++p16)
        {
            p4=*p16;
            if(tag)p4->p=p4->p_u;
            else
            {
                p_tmp=p_tmp1;err1=err2;
                sum_p(&p_tmp1,&err2,p4->p_l);
                if(p_tmp1>p4->p_u)
                {
                    p4->p=p4->p_l;
                    sum_m(&p_tmp1,&err2,p4->p_u);
                }
                else
                {
                    p4->p=p4->p_u;err2=0;
                    sum_m(&p4->p,&err2,p_tmp);
                    sum_m(&p4->p,&err2,err1);
                    tag=2;
                }
//                p_tmp=p4->p_u-p4->p_l;
//                if(p2->p>p_tmp)
//                {
//                    p4->p=p4->p_l;
//                    p2->p-=p_tmp;
//                }
//                else{p4->p=p4->p_u-p2->p;tag=2;}
            }
        }
    }
    end_t=clock();
    printf("Time used to build data structure for iterative method = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    
    // MARK: Solve x = Ax + b
    start_t=clock();
    printf("Solve x = Ax + b:\n");
    for(cnt3=0,j=1;;++j)
    {
        for(i=1;i<=ITERATION_BOUND;++i)
        {
            p7=decode_max;p11=b_vec;
            p16=p17=sort_edge;
            p12=x_current;p13=x_next;
            err_max=0.0;max_rel_err=0.0;cnt2=0;cnt1=1<<31;
            for(;p7!=p8;++p7,++p11,++p12,++p13)
            {
                p4=*(out_pos+*p7);
                if(!p4){*p13=*p11;continue;}
                for(*p13=p4->p,err2=0.0,p17=p16+p4->num;p16!=p17;++p16)
                {
                    p_tmp=*(x_current+(*p16)->x2)*(*p16)->p;
                    sum_p(p13,&err2,p_tmp);
                }
                sum_p(p13,&err2,*p11);
                
                p_tmp=*p13*EPS;
                sum_p(p13,&err2,p_tmp);
                
                
//                for(*p13=0,p17=p16+p4->num;p16!=p17;++p16)
//                    *p13+=*(x_current+(*p16)->x2)*(*p16)->p;
//                *p13+=*p11;
                
                p_tmp=*p13-*p12;
                if(p_tmp&&p4->x2)
                {
                    if((p_tmp>0)^(p4->x2&1))p4->x2>>=1;
                    else CLR_BIT(p4->x2,0);
                    for(;;)
                    {
                        p_tmp1=*p13+p_tmp*p4->x2/(1<<15);
                        if(p_tmp1>1||p_tmp1<0)
                            p4->x2>>=1;
                        else break;
                    }
                    
                    if(p4->x2)
                    {
                        p_tmp*=p4->x2;
                        p_tmp/=(1<<15);
                        sum_p(p13,&err2,p_tmp);
                        if(p_tmp<0)
                            SET_BIT(p4->x2,0);
                    }else p4->x2=1<<2;
                    if(p4->x2>cnt2)cnt2=p4->x2;
                    if(p4->x2<cnt1)cnt1=p4->x2;
                }
                
//                if(*p13+*p13*MACHINE_EPSILON<*p12)printf("Unexpected, not monotone increasing: node[%u]: x_current: %.17e difference: %.3e.\n",*p7,*p12,(*p12-*p13)/MACHINE_EPSILON);
//                
//                if(*p13<*p12)++cnt2;
                
//                if(*p13<*p12)*p13=*p12;
                
                err_current=fabs(*p13-*p12);
                if(err_current>err_max)err_max=err_current;
                if(err_current!=0.0)
                {
                    p_tmp=err_current/(__DBL_EPSILON__**p13);
                    if(p_tmp>max_rel_err)max_rel_err=p_tmp;
                }
                
                
            }
            printf("Max multiplier = %e, min multiplier = %e.\n",1.0*cnt2/(1<<15),1.0*cnt1/(1<<15));
            
            
//            if(cnt2)
//            printf("#: %u\t",cnt2);
            //swap x_current and x_next
            x_tmp=x_current;
            x_current=x_next;
            x_next=x_tmp;
            if(i==1)
            {
                printf("Error_max after shift = %.17e.\t",err_max);
//                printf("#: %u\t",cnt2);
            }
            
            if(err_max1<err_max)printf("Inner # %u: relative error violation: %.17e, current error: %.17e, previous error: %.17e.\n",i,(err_max-err_max1)/err_max,err_max,err_max1);
            err_max1=err_max;
            
//            if(err_max<=EPSILON)break;
            
//            printf("max_rel_err = %.17e.\n",max_rel_err);
            if(max_rel_err<REL_ERR_THRES)break;
        }
        printf("max_rel_err = %.17e.\n",max_rel_err);
        printf("%u th iteration: ",j);
        if(i<=ITERATION_BOUND)printf("# of iterations: %u.",i);
        else printf("# of iterations exceeds ITERATION_BOUND %u.",ITERATION_BOUND);
        printf("\t err_max = %.17e.",err_max);
        cnt3+=i;
        if(i>ITERATION_BOUND)--cnt3;
        for(p14=sort_x,p15=p14+l2,p11=*p14,++p14;p14!=p15;++p14)
        {
            p12=*p14;
            if(*p11<=*p12)p11=p12;
            else break;
        }
        printf("\t%u\n",(uint32_t)(p14-sort_x));
        if(p14==p15)
        {
            if(i>ITERATION_BOUND){printf("Order doesn't change but needs more iterations.\n");continue;}
            else break;
        }
        
        qsort(sort_x,l2,sizeof(double*),cmp1);
        for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
            *(*p14-x_vec+permutation)=cnt2;
        // assign probability to edges
        p16=p17=sort_edge;
        for(p7=decode_max;p7!=p8;++p7)
        {
            p2=*(out_pos+*p7);
            if(!p2)continue;
            if(p2->p_u==0.0)
            {p16=p17+=p2->num;continue;}
            for(p18=p17+p2->num,p3=*p17,++p17;p17!=p18;++p17)
            {
                p4=*p17;
                if(*(permutation+p3->x2)<*(permutation+p4->x2))p3=p4;
                else break;
            }
            if(p17==p18){p16=p18;continue;}
            else p17=p18;
            qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
            for(p_tmp1=p2->p_u,err2=p2->p_l,tag=0;p16!=p17;++p16)
            {
                p4=*p16;
                if(tag)p4->p=p4->p_u;
                else
                {
                    p_tmp=p_tmp1;err1=err2;
                    sum_p(&p_tmp1,&err2,p4->p_l);
                    if(p_tmp1>p4->p_u)
                    {
                        p4->p=p4->p_l;
                        sum_m(&p_tmp1,&err2,p4->p_u);
                    }
                    else
                    {
                        p4->p=p4->p_u;err2=0;
                        sum_m(&p4->p,&err2,p_tmp);
                        sum_m(&p4->p,&err2,err1);
                        tag=2;
                    }
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p>p_tmp)
//                    {
//                        p4->p=p4->p_l;
//                        p2->p-=p_tmp;
//                    }
//                    else{p4->p=p4->p_u-p2->p;tag=2;}
                }
            }
        }
    }
    
    printf("# of outer loop iterations :%u\n",j);
    printf("# of total loop iterations :%u\n",cnt3);
    
    for(p11=b_vec,p12=p11+l2,p13=x_current;p11!=p12;++p11,++p13)
        *p11=*p13;
    head->x_vec_power_max=b_vec;
    imc->b_vec=0;
    free(x_vec);imc->x_vec=0;
    free(sort_edge);imc->sort_edge=0;
    
    
//    free(out_pos);imc->out_pos=0;
//    free(imc->out_edge);imc->out_edge=0;
//    free(decode1);head->decode1=0;
//    free(b_vec);imc->b_vec=0;
    end_t=clock();
    printf("Time used to solve x = Ax + b = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("Time used to solve quantitative maximum reachability using power method = %.4f\n",
           (double)(end_t-start_t0)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void reset_imc(HEAD *head,BOOL tag)
{
    IMC *imc;
    
    uint32_t n0,*decode,*p7,*p8,l2;
    OUT_EDGE **out_pos,**out_pos_reset,**p4,*p3,*p5;
    clock_t start_t0,start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    out_pos=imc->out_pos;
    p3=imc->out_edge;
    out_pos_reset=imc->out_pos_reset;
    n0=imc->n;
    if(tag<3)
    {
        l2=head->l2_max;
        decode=head->decode_max;
    }
    else
    {
        l2=head->l2_min;
        decode=head->decode_min;
    }
    printf("Reset imc_post\n");
    
    // MARK: reset imc_post
    start_t0=start_t=clock();

    for(p7=decode,p8=p7+l2;p7!=p8;++p7)
    {
        if(*(out_pos+*p7))
        {
            p5=p3=*(out_pos+*p7);
            for(;p5->next;)
            {
                p5+=p5->next;
                p5->x2=*(decode+p5->x2);
            }
        }
        else p3=*(out_pos+*p7)=*(out_pos_reset+*p7);
        p4=out_pos_reset+*p7;
        ++p4;
        p5=*p4-1;
        for(;p3!=p5;++p3)
            p3->next=1;
        p3->next=0;
    }
    if(tag&1)
    {
        if(permutation)free(permutation);permutation=0;
        if(imc->sort_x)free(imc->sort_x);imc->sort_x=0;
    }
    end_t=clock();
    printf("Time used to reset imc_post = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("********\n\n");
    
}

void solve_quantitative_min_reachability_power_method(HEAD *head)
{
    IMC *imc;
    uint32_t n0,l2,cnt2,cnt3;
    uint32_t i,j;
    uint64_t cnt1;
    OUT_EDGE **out_pos,**sort_edge,*p2,*p3,*p4,**p16,**p17,**p18;
    uint32_t *encode_min,*decode_min,*p5,*p6,*p7,*p8;
    double err1,err2,p_tmp,p_tmp1,*x_vec,*b_vec,*p11,*p12,*p13,*x_current,*x_next,*x_tmp,err_current,err_max = 0.0,**sort_x,**p14,**p15;
    BOOL *flag,*p9,tag;
    clock_t start_t0,start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    out_pos=imc->out_pos;
    flag=head->flag_min;
    n0=imc->n;
    l2=head->l2_min;
    
    printf("Solve quantitative minimum reachability using power method:\n");
    
    // MARK: build data structure for iterative method
    start_t0=start_t=clock();
    printf("Build data structure for iterative method:\n");
    if(!l2)
    {
        printf("All states have trivial probability 0 or 1, so no quantitative minimum reachability needs to be solved.\n");
        return;
    }
    // Encode and decode
    if(head->encode_min)
    {
        encode_min=head->encode_min;
        decode_min=head->decode_min;
        p8=decode_min+l2;
    }
    else
    {
        head->encode_min=encode_min=imc->queue;imc->queue=0;
        head->decode_min=decode_min=(uint32_t*)malloc(l2*sizeof(uint32_t));
        p5=encode_min;p7=decode_min;p9=flag;
        for(p6=p5+n0;p5!=p6;++p5,++p9)
            if(*p9==2)
            {
                *p5=(uint32_t)(p7-decode_min);
                *p7=(uint32_t)(p5-encode_min);++p7;
            }
            else *p5=n0;
    }
    // Compute sum_l and sum_u
    for(p7=decode_min,p8=p7+l2;p7!=p8;++p7)
    {
        p2=p4=*(out_pos+*p7);
        for(p2->p=p2->p_l=p2->p_u=err1=err2=0.0;p4->next;)
        {
            p4+=p4->next;
            sum_p(&p2->p_l,&err1,p4->p_l);
            sum_p(&p2->p_u,&err2,p4->p_u);
//            p2->p_l+=p4->p_l;
//            p2->p_u+=p4->p_u;
        }
        // Sterbenz's lemma
        p_tmp=p2->p_l;p2->p_l=1.0;
        sum_m(&p2->p_l,&p2->p,p_tmp);
        sum_m(&p2->p_l,&p2->p,err1);
        
        sum_m(&p2->p_u,&err2,1.0);
        p2->p_u+=err2;
//        p2->p_l=1.0-p2->p_l;p2->p_u-=1.0;
    }
    // Set up x = Ax + b
    p11=imc->b_vec=b_vec=(double*)calloc(l2,sizeof(double));
    for(p7=decode_min,cnt1=0;p7!=p8;++p7,++p11)
    {
        p2=p3=p4=*(out_pos+*p7);
        err1=p2->p;
        err2=p2->p=0.0;
        for(p2->num=tag=0;p4->next;)
        {
            p4+=p4->next;
            p9=flag+p4->x2;
            if(*p9==2)
            {p3=p4;++p2->num;p4->x2=*(encode_min+p4->x2);}
            else
            {
                p3->next+=p4->next;
                if(*p9&1)// label == 1 || 3
                {
                    switch(tag)
                    {
                        case 0:
                        {
                            p_tmp=p2->p_u;p_tmp1=err2;
                            sum_p(&p2->p_u,&err2,p4->p_l);
                            if(p2->p_u>p4->p_u)
                            {
                                sum_p(p11,&p2->p,p4->p_l);
                                sum_m(&p2->p_u,&err2,p4->p_u);
                            }
                            else
                            {
                                sum_p(p11,&p2->p,p4->p_u);
                                sum_m(p11,&p2->p,p_tmp);
                                sum_m(p11,&p2->p,p_tmp1);
                                tag=1;
                            }
//                            p_tmp=p4->p_u-p4->p_l;
//                            if(p2->p_u>p_tmp)
//                            {
//                                *p11+=p4->p_l;
//                                p2->p_u-=p_tmp;
//                            }
//                            else
//                            {*p11+=p4->p_u-p2->p_u;tag=1;}
                        }
                        break;
                        case 1:
                        sum_p(p11,&p2->p,p4->p_u);
//                        *p11+=p4->p_u;
                        break;
                        case 2:
                        sum_p(p11,&p2->p,p4->p_l);
//                        *p11+=p4->p_l;
                    }
                }
                else if(!tag)
                {
                    sum_p(&p2->p_l,&err1,p4->p_l);
                    if(p2->p_l>p4->p_u)
                    sum_m(&p2->p_l,&err1,p4->p_u);
                    else tag=2;
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p_l>p_tmp)
//                    {p2->p_l-=p_tmp;}
//                    else{tag=2;}
                }
            }
        }
        if(p3!=p2)p3->next=0;else p2=0;
        if(!p2)continue;
        cnt1+=p2->num;
        if(tag)
        {
            p2->p_l=0.0;
            if(tag&1)
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_u;}
            else
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_l;}
        }else{p2->p_u=err1;}
    }
    printf("Size of iteration matrix = n + m = %u + %llu = %llu.\n",l2,cnt1,l2+cnt1);
    printf("Size of sort_edge = %llu.\n",cnt1);
    imc->x_vec=x_vec=(double*)malloc((l2<<1)*sizeof(double));//l2*2
    if(imc->sort_x)sort_x=imc->sort_x;
    else
    {
        imc->sort_x=sort_x=(double**)malloc(l2*sizeof(double*));
    }
    // x(0)=0, x(1)=b
    p11=b_vec;p12=p11+l2;p13=x_vec;p14=sort_x;
    for(;p11!=p12;++p11,++p13,++p14)
    {*p13=*p11;*p14=p13;}
    x_current=x_vec;x_next=x_vec+l2;
    // Sort x(1)
    qsort(sort_x,l2,sizeof(double*),cmp1);
    if(!permutation)
    permutation=(uint32_t*)malloc(l2*sizeof(uint32_t));
    for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
        *(*p14-x_vec+permutation)=cnt2;
    
    p16=p17=imc->sort_edge=sort_edge=(OUT_EDGE**)malloc(cnt1*sizeof(OUT_EDGE*));
    // assign probability to edges
    for(p7=decode_min;p7!=p8;++p7)
    {
        p2=p4=*(out_pos+*p7);
        if(!p2)continue;
        for(;p4->next;++p17)
        {p4+=p4->next;*p17=p4;}
        qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
        if(p2->p_l==0.0){p16=p17;continue;}
        for(p_tmp1=p2->p_l,err1=p2->p_u,tag=0;p16!=p17;++p16)
        {
            p4=*p16;
            if(tag)p4->p=p4->p_l;
            else
            {
                sum_p(&p_tmp1,&err1,p4->p_l);
                if(p_tmp1>p4->p_u)
                {
                    p4->p=p4->p_u;
                    sum_m(&p_tmp1,&err1,p4->p_u);
                }
                else{p4->p=p_tmp1;tag=2;}
//                p_tmp=p4->p_u-p4->p_l;
//                if(p2->p>p_tmp)
//                {
//                    p4->p=p4->p_u;
//                    p2->p-=p_tmp;
//                }
//                else{p4->p=p4->p_l+p2->p;tag=2;}
            }
        }
    }
    end_t=clock();
    printf("Time used to build data structure for iterative method = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    
    // MARK: Solve x = Ax + b
    start_t=clock();
    printf("Solve x = Ax + b:\n");
    
    p13=x_vec;
    for(p12=p13+l2;p13!=p12;++p13)
    *p13=1.0;
    
    for(cnt3=0,j=1;;++j)
    {
        for(i=1;i<=ITERATION_BOUND;++i)
        {
            p7=decode_min;p11=b_vec;
            p16=p17=sort_edge;
            p12=x_current;p13=x_next;
            err_max=0.0;
            for(;p7!=p8;++p7,++p11,++p12,++p13)
            {
                p4=*(out_pos+*p7);
                if(!p4){*p13=*p11;continue;}
                for(*p13=p4->p,err1=0.0,p17=p16+p4->num;p16!=p17;++p16)
                {
                    p_tmp=*(x_current+(*p16)->x2)*(*p16)->p;
                    sum_p(p13,&err1,p_tmp);
                }
                sum_p(p13,&err1,*p11);
                
//                for(*p13=0,p17=p16+p4->num;p16!=p17;++p16)
//                    *p13+=*(x_current+(*p16)->x2)*(*p16)->p;
//                *p13+=*p11;
                
                if(*p12+1*MACHINE_EPSILON<*p13)printf("Unexpected, not monotone decreasing: node[%u]: x_current: %.17e difference: %.3e.\n",*p7,*p12,(*p13-*p12)/MACHINE_EPSILON);
                
//                if(err_max<=EPSILON&&*p13>*p12)*p13=*p12;
                
                err_current=fabs(*p13-*p12);
                if(err_current>err_max)err_max=err_current;
            }
            //swap x_current and x_next
            x_tmp=x_current;
            x_current=x_next;
            x_next=x_tmp;
            if(i==1)printf("Error_max after shift = %.17e.\t",err_max);
            if(err_max<=EPSILON)break;
        }
        printf("%u th iteration: ",j);
        if(i<=ITERATION_BOUND)printf("# of iterations: %u.",i);
        else printf("# of iterations exceeds ITERATION_BOUND %u.",ITERATION_BOUND);
        printf("\t err_max = %.17e.",err_max);
        cnt3+=i;
        if(i>ITERATION_BOUND)--cnt3;
        for(p14=sort_x,p15=p14+l2,p11=*p14,++p14;p14!=p15;++p14)
        {
            p12=*p14;
//            if(*p11<=*p12+MACHINE_EPSILON)p11=p12;
            if(*p11<=*p12)p11=p12;
            else break;
        }
        printf("\t%u\n",(uint32_t)(p14-sort_x));
        if(p14==p15)
        {
            if(i>ITERATION_BOUND){printf("Order doesn't change but needs more iterations.\n");continue;}
            else break;
        }
        
        qsort(sort_x,l2,sizeof(double*),cmp1);
        for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
            *(*p14-x_vec+permutation)=cnt2;
        // assign probability to edges
        p16=p17=sort_edge;
        for(p7=decode_min;p7!=p8;++p7)
        {
            p2=*(out_pos+*p7);
            if(!p2)continue;
            if(p2->p_l==0.0)
            {p16=p17+=p2->num;continue;}
            for(p18=p17+p2->num,p3=*p17,++p17;p17!=p18;++p17)
            {
                p4=*p17;
                if(*(permutation+p3->x2)<*(permutation+p4->x2))p3=p4;
                else break;
            }
            if(p17==p18){p16=p18;continue;}
            else p17=p18;
            qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
            for(p_tmp1=p2->p_l,err1=p2->p_u,tag=0;p16!=p17;++p16)
            {
                p4=*p16;
                if(tag)p4->p=p4->p_l;
                else
                {
                    sum_p(&p_tmp1,&err1,p4->p_l);
                    if(p_tmp1>p4->p_u)
                    {
                        p4->p=p4->p_u;
                        sum_m(&p_tmp1,&err1,p4->p_u);
                    }
                    else{p4->p=p_tmp1;tag=2;}
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p>p_tmp)
//                    {
//                        p4->p=p4->p_u;
//                        p2->p-=p_tmp;
//                    }
//                    else{p4->p=p4->p_l+p2->p;tag=2;}
                }
            }
        }
    }
    
    printf("# of outer loop iterations :%u\n",j);
    printf("# of total loop iterations :%u\n",cnt3);
    
    for(p11=b_vec,p12=p11+l2,p13=x_current;p11!=p12;++p11,++p13)
        *p11=*p13;
    head->x_vec_power_min=b_vec;
    imc->b_vec=0;
    free(x_vec);imc->x_vec=0;
    free(sort_edge);imc->sort_edge=0;
    
//    free(out_pos);imc->out_pos=0;
//    free(imc->out_edge);imc->out_edge=0;
//    free(decode1);head->decode1=0;
//    free(b_vec);imc->b_vec=0;
    end_t=clock();
    printf("Time used to solve x = Ax + b = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("Time used to solve quantitative minimum reachability using power method = %.4f\n",
           (double)(end_t-start_t0)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void solve_quantitative_min_reachability_Jacobi_method(HEAD *head)
{
    IMC *imc;
    uint32_t n0,l2,cnt2,cnt3;
    uint32_t i,j;
    uint64_t cnt1;
    OUT_EDGE **out_pos,**sort_edge,*p2,*p3,*p4,**p16,**p17,**p18;
    uint32_t *encode_min,*decode_min,*p5,*p6,*p7,*p8;
    double err1,err2,p_tmp,p_tmp1,*x_vec,*b_vec,*p11,*p12,*p13,*x_current,*x_next,*x_tmp,err_current,err_max = 0.0,**sort_x,**p14,**p15;
    BOOL *flag,*p9,tag;
    clock_t start_t0,start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    out_pos=imc->out_pos;
    flag=head->flag_min;
    n0=imc->n;
    l2=head->l2_min;
    
    printf("Solve quantitative minimum reachability using Jacobi method:\n");
    
    // MARK: build data structure for iterative method
    start_t0=start_t=clock();
    printf("Build data structure for iterative method:\n");
    if(!l2)
    {
        printf("All states have trivial probability 0 or 1, so no quantitative minimum reachability needs to be solved.\n");
        return;
    }
    // Encode and decode
    if(head->encode_min)
    {
        encode_min=head->encode_min;
        decode_min=head->decode_min;
        p8=decode_min+l2;
    }
    else
    {
        head->encode_min=encode_min=imc->queue;imc->queue=0;
        head->decode_min=decode_min=(uint32_t*)malloc(l2*sizeof(uint32_t));
        p5=encode_min;p7=decode_min;p9=flag;
        for(p6=p5+n0;p5!=p6;++p5,++p9)
            if(*p9==2)
            {
                *p5=(uint32_t)(p7-decode_min);
                *p7=(uint32_t)(p5-encode_min);++p7;
            }
            else *p5=n0;
    }
    // Compute sum_l and sum_u
    for(p7=decode_min,p8=p7+l2;p7!=p8;++p7)
    {
        p2=p4=*(out_pos+*p7);
        for(p2->p=p2->p_l=p2->p_u=err1=err2=0.0;p4->next;)
        {
            p4+=p4->next;
            sum_p(&p2->p_l,&err1,p4->p_l);
            sum_p(&p2->p_u,&err2,p4->p_u);
//            p2->p_l+=p4->p_l;
//            p2->p_u+=p4->p_u;
        }
        // Sterbenz's lemma
        p_tmp=p2->p_l;p2->p_l=1.0;
        sum_m(&p2->p_l,&p2->p,p_tmp);
        sum_m(&p2->p_l,&p2->p,err1);
        
        sum_m(&p2->p_u,&err2,1.0);
        p2->p_u+=err2;
//        p2->p_l=1.0-p2->p_l;p2->p_u-=1.0;
    }
    // Set up (I-D)x = (L+U)x + b
    p11=imc->b_vec=b_vec=(double*)calloc(l2,sizeof(double));
    for(p7=decode_min,cnt1=0;p7!=p8;++p7,++p11)
    {
        p2=p3=p4=*(out_pos+*p7);
        err1=p2->p;
        err2=p2->p=0.0;
        for(p2->x2=p2->num=tag=0;p4->next;)
        {
            p4+=p4->next;
            p9=flag+p4->x2;
            if(*p9==2)
            {
                p3=p4;++p2->num;
                if(*p7==p4->x2)p2->x2=(uint32_t)(p4-p2);
                p4->x2=*(encode_min+p4->x2);
            }
            else
            {
                p3->next+=p4->next;
                if(*p9&1)// label == 1 || 3
                {
                    switch(tag)
                    {
                        case 0:
                        {
                            p_tmp=p2->p_u;p_tmp1=err2;
                            sum_p(&p2->p_u,&err2,p4->p_l);
                            if(p2->p_u>p4->p_u)
                            {
                                sum_p(p11,&p2->p,p4->p_l);
                                sum_m(&p2->p_u,&err2,p4->p_u);
                            }
                            else
                            {
                                sum_p(p11,&p2->p,p4->p_u);
                                sum_m(p11,&p2->p,p_tmp);
                                sum_m(p11,&p2->p,p_tmp1);
                                tag=1;
                            }
//                            p_tmp=p4->p_u-p4->p_l;
//                            if(p2->p_u>p_tmp)
//                            {
//                                *p11+=p4->p_l;
//                                p2->p_u-=p_tmp;
//                            }
//                            else
//                            {*p11+=p4->p_u-p2->p_u;tag=1;}
                        }
                        break;
                        case 1:
                        sum_p(p11,&p2->p,p4->p_u);
//                        *p11+=p4->p_u;
                        break;
                        case 2:
                        sum_p(p11,&p2->p,p4->p_l);
//                        *p11+=p4->p_l;
                    }
                }
                else if(!tag)
                {
                    sum_p(&p2->p_l,&err1,p4->p_l);
                    if(p2->p_l>p4->p_u)
                    sum_m(&p2->p_l,&err1,p4->p_u);
                    else tag=2;
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p_l>p_tmp)
//                    {p2->p_l-=p_tmp;}
//                    else{tag=2;}
                }
            }
        }
        if(p3!=p2)p3->next=0;else p2=0;
        if(!p2)continue;
        cnt1+=p2->num;
        if(tag)
        {
            p2->p_l=0.0;
            if(tag&1)
            {
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_u;}
                if(p2->x2)
                {p4=p2+p2->x2;p4->p=1.0/(1-p4->p_u);}
            }
            else
            {
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_l;}
                if(p2->x2)
                {p4=p2+p2->x2;p4->p=1.0/(1-p4->p_l);}
            }
        }else{p2->p_u=err1;}
    }
    printf("Size of iteration matrix = n + m = %u + %llu = %llu.\n",l2,cnt1,l2+cnt1);
    printf("Size of sort_edge = %llu.\n",cnt1);
    imc->x_vec=x_vec=(double*)malloc((l2<<1)*sizeof(double));//l2*2
    if(imc->sort_x)sort_x=imc->sort_x;
    else
    {
        imc->sort_x=sort_x=(double**)malloc(l2*sizeof(double*));
    }
    // x(0)=0, x(1)=b(for sort)
    p11=b_vec;p12=p11+l2;p13=x_vec;p14=sort_x;
    for(;p11!=p12;++p11,++p13,++p14)
    {*p13=*p11;*p14=p13;}
    x_current=x_vec;x_next=x_vec+l2;
    // Sort x(1)
    qsort(sort_x,l2,sizeof(double*),cmp1);
    if(!permutation)
    permutation=(uint32_t*)malloc(l2*sizeof(uint32_t));
    for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
        *(*p14-x_vec+permutation)=cnt2;
    
    p16=p17=imc->sort_edge=sort_edge=(OUT_EDGE**)malloc(cnt1*sizeof(OUT_EDGE*));
    // assign probability to edges, x(1)=(I-D)^{-1}b
    for(p7=decode_min,p13=x_vec;p7!=p8;++p7,++p13)
    {
        p2=p4=*(out_pos+*p7);
        if(!p2)continue;
        for(;p4->next;++p17)
        {p4+=p4->next;*p17=p4;}
        qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
        if(p2->p_l==0.0)
        {
            p16=p17;
            if(p2->x2)
            {
                p4=p2+p2->x2;*p13*=p4->p;
                err1=p2->p*p4->p;*p13+=err1;
            }
            continue;
        }
        for(p_tmp1=p2->p_l,err1=p2->p_u,tag=0;p16!=p17;++p16)
        {
            p4=*p16;
            if(tag)p4->p=p4->p_l;
            else
            {
                sum_p(&p_tmp1,&err1,p4->p_l);
                if(p_tmp1>p4->p_u)
                {
                    p4->p=p4->p_u;
                    sum_m(&p_tmp1,&err1,p4->p_u);
                }
                else{p4->p=p_tmp1;tag=2;}
//                p_tmp=p4->p_u-p4->p_l;
//                if(p2->p>p_tmp)
//                {
//                    p4->p=p4->p_u;
//                    p2->p-=p_tmp;
//                }
//                else{p4->p=p4->p_l+p2->p;tag=2;}
            }
        }
        if(p2->x2)
        {
            p4=p2+p2->x2;
            p4->p=1.0/(1-p4->p);
            *p13*=p4->p;
            err1=p2->p*p4->p;*p13+=err1;
        }
    }
    end_t=clock();
    printf("Time used to build data structure for iterative method = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    
    // MARK: Solve (I-D)x = (L+U)x + b
    start_t=clock();
    printf("Solve (I-D)x = (L+U)x + b:\n");
    
    p13=x_vec;
    for(p12=p13+l2;p13!=p12;++p13)
    *p13=1.0;
    
    for(cnt3=0,j=1;;++j)
    {
        for(i=1;i<=ITERATION_BOUND;++i)
        {
            p7=decode_min;p11=b_vec;
            p16=p17=sort_edge;
            p12=x_current;p13=x_next;
            err_max=0.0;
            for(;p7!=p8;++p7,++p11,++p12,++p13)
            {
                p2=p4=*(out_pos+*p7);
                if(!p4){*p13=*p11;continue;}
                if(p2->x2)
                {
                    p3=p2+p2->x2;
                    *p13=p4->p;err1=0.0;p17=p16+p4->num;
                    for(;p16!=p17;++p16)
                        if(*p16!=p3)
                        {
                            p_tmp=*(x_current+(*p16)->x2)*(*p16)->p;
                            sum_p(p13,&err1,p_tmp);
                        }
                    sum_p(p13,&err1,*p11);
                    *p13*=p3->p;err1*=p3->p;*p13+=err1;
                    
//                    p3=p2+p2->x2;
//                    *p13=0;p17=p16+p4->num;
//                    for(;p16!=p17;++p16)
//                        if(*p16!=p3)*p13+=*(x_current+(*p16)->x2)*(*p16)->p;
//                    *p13+=*p11;*p13*=p3->p;
                }
                else
                {
                    *p13=p4->p;err1=0.0;p17=p16+p4->num;
                    for(;p16!=p17;++p16)
                    {
                        p_tmp=*(x_current+(*p16)->x2)*(*p16)->p;
                        sum_p(p13,&err1,p_tmp);
                    }
                    sum_p(p13,&err1,*p11);
                    
//                    *p13=0;p17=p16+p4->num;
//                    for(;p16!=p17;++p16)
//                    *p13+=*(x_current+(*p16)->x2)*(*p16)->p;
//                    *p13+=*p11;
                }
                
                if(*p12+4*MACHINE_EPSILON<*p13)printf("Unexpected, not monotone decreasing: node[%u]: x_current: %.17e difference: %.3e.\n",*p7,*p12,(*p13-*p12)/MACHINE_EPSILON);
                
//                if(*p13>*p12)*p13=*p12;
                
                err_current=fabs(*p13-*p12);
                if(err_current>err_max)err_max=err_current;
            }
            //swap x_current and x_next
            x_tmp=x_current;
            x_current=x_next;
            x_next=x_tmp;
            if(i==1)printf("Error_max after shift = %.17e.\t",err_max);
            if(err_max<=EPSILON)break;
        }
        printf("%u th iteration: ",j);
        if(i<=ITERATION_BOUND)printf("# of iterations: %u.",i);
        else printf("# of iterations exceeds ITERATION_BOUND %u.",ITERATION_BOUND);
        printf("\t err_max = %.17e.\n",err_max);
        cnt3+=i;
        if(i>ITERATION_BOUND)--cnt3;
        for(p14=sort_x,p15=p14+l2,p11=*p14,++p14;p14!=p15;++p14)
        {
            p12=*p14;
//            if(*p11<=*p12+MACHINE_EPSILON)p11=p12;
            if(*p11<=*p12)p11=p12;
            else break;
        }
        printf("\t%u\n",(uint32_t)(p14-sort_x));
        if(p14==p15)
        {
            if(i>ITERATION_BOUND){printf("Order doesn't change but needs more iterations.\n");continue;}
            else break;
        }
        
        qsort(sort_x,l2,sizeof(double*),cmp1);
        for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
            *(*p14-x_vec+permutation)=cnt2;
        // assign probability to edges
        p16=p17=sort_edge;
        for(p7=decode_min;p7!=p8;++p7)
        {
            p2=*(out_pos+*p7);
            if(!p2)continue;
            if(p2->p_l==0.0)
            {p16=p17+=p2->num;continue;}
            for(p18=p17+p2->num,p3=*p17,++p17;p17!=p18;++p17)
            {
                p4=*p17;
                if(*(permutation+p3->x2)<*(permutation+p4->x2))p3=p4;
                else break;
            }
            if(p17==p18){p16=p18;continue;}
            else p17=p18;
            qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
            for(p_tmp1=p2->p_l,err1=p2->p_u,tag=0;p16!=p17;++p16)
            {
                p4=*p16;
                if(tag)p4->p=p4->p_l;
                else
                {
                    sum_p(&p_tmp1,&err1,p4->p_l);
                    if(p_tmp1>p4->p_u)
                    {
                        p4->p=p4->p_u;
                        sum_m(&p_tmp1,&err1,p4->p_u);
                    }
                    else{p4->p=p_tmp1;tag=2;}
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p>p_tmp)
//                    {
//                        p4->p=p4->p_u;
//                        p2->p-=p_tmp;
//                    }
//                    else{p4->p=p4->p_l+p2->p;tag=2;}
                }
            }
            if(p2->x2)
            {p4=p2+p2->x2;p4->p=1.0/(1-p4->p);}
        }
    }
    
    printf("# of outer loop iterations :%u\n",j);
    printf("# of total loop iterations :%u\n",cnt3);
    
    for(p11=b_vec,p12=p11+l2,p13=x_current;p11!=p12;++p11,++p13)
        *p11=*p13;
    head->x_vec_Jacobi_min=b_vec;
    imc->b_vec=0;
    free(x_vec);imc->x_vec=0;
    free(sort_edge);imc->sort_edge=0;
    
//    free(out_pos);imc->out_pos=0;
//    free(imc->out_edge);imc->out_edge=0;
//    free(decode1);head->decode1=0;
//    free(b_vec);imc->b_vec=0;
    end_t=clock();
    printf("Time used to solve (I-D)x = (L+U)x + b = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("Time used to solve quantitative minimum reachability using Jacobi method = %.4f\n",
           (double)(end_t-start_t0)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void solve_quantitative_min_reachability_Gauss_Seidel_method(HEAD *head)
{
    IMC *imc;
    uint32_t n0,l2,cnt2,cnt3;
    uint32_t i,j;
    uint64_t cnt1;
    OUT_EDGE **out_pos,**sort_edge,*p2,*p3,*p4,**p16,**p17,**p18;
    uint32_t *encode_min,*decode_min,*p5,*p6,*p7,*p8;
    double err1,err2,p_tmp,p_tmp1,*x_vec,*b_vec,*p11,*p12,*p13,x_current,err_current,err_max = 0.0,**sort_x,**p14,**p15;
    BOOL *flag,*p9,tag;
    clock_t start_t0,start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    out_pos=imc->out_pos;
    flag=head->flag_min;
    n0=imc->n;
    l2=head->l2_min;
    
    printf("Solve quantitative minimum reachability using Gauss Seidel method:\n");
    
    // MARK: build data structure for iterative method
    start_t0=start_t=clock();
    printf("Build data structure for iterative method:\n");
    if(!l2)
    {
        printf("All states have trivial probability 0 or 1, so no quantitative minimum reachability needs to be solved.\n");
        return;
    }
    // Encode and decode
    if(head->encode_min)
    {
        encode_min=head->encode_min;
        decode_min=head->decode_min;
        p8=decode_min+l2;
    }
    else
    {
        head->encode_min=encode_min=imc->queue;imc->queue=0;
        head->decode_min=decode_min=(uint32_t*)malloc(l2*sizeof(uint32_t));
        p5=encode_min;p7=decode_min;p9=flag;
        for(p6=p5+n0;p5!=p6;++p5,++p9)
            if(*p9==2)
            {
                *p5=(uint32_t)(p7-decode_min);
                *p7=(uint32_t)(p5-encode_min);++p7;
            }
            else *p5=n0;
    }
    // Compute sum_l and sum_u
    for(p7=decode_min,p8=p7+l2;p7!=p8;++p7)
    {
        p2=p4=*(out_pos+*p7);
        for(p2->p=p2->p_l=p2->p_u=err1=err2=0.0;p4->next;)
        {
            p4+=p4->next;
            sum_p(&p2->p_l,&err1,p4->p_l);
            sum_p(&p2->p_u,&err2,p4->p_u);
//            p2->p_l+=p4->p_l;
//            p2->p_u+=p4->p_u;
        }
        // Sterbenz's lemma
        p_tmp=p2->p_l;p2->p_l=1.0;
        sum_m(&p2->p_l,&p2->p,p_tmp);
        sum_m(&p2->p_l,&p2->p,err1);
        
        sum_m(&p2->p_u,&err2,1.0);
        p2->p_u+=err2;
//        p2->p_l=1.0-p2->p_l;p2->p_u-=1.0;
    }
    // Set up (I-D-L)x = Ux + b
    p11=imc->b_vec=b_vec=(double*)calloc(l2,sizeof(double));
    for(p7=decode_min,cnt1=0;p7!=p8;++p7,++p11)
    {
        p2=p3=p4=*(out_pos+*p7);
        err1=p2->p;
        err2=p2->p=0.0;
        for(p2->x2=p2->num=tag=0;p4->next;)
        {
            p4+=p4->next;
            p9=flag+p4->x2;
            if(*p9==2)
            {
                p3=p4;++p2->num;
                if(*p7==p4->x2)p2->x2=(uint32_t)(p4-p2);
                p4->x2=*(encode_min+p4->x2);
            }
            else
            {
                p3->next+=p4->next;
                if(*p9&1)// label == 1 || 3
                {
                    switch(tag)
                    {
                        case 0:
                        {
                            p_tmp=p2->p_u;p_tmp1=err2;
                            sum_p(&p2->p_u,&err2,p4->p_l);
                            if(p2->p_u>p4->p_u)
                            {
                                sum_p(p11,&p2->p,p4->p_l);
                                sum_m(&p2->p_u,&err2,p4->p_u);
                            }
                            else
                            {
                                sum_p(p11,&p2->p,p4->p_u);
                                sum_m(p11,&p2->p,p_tmp);
                                sum_m(p11,&p2->p,p_tmp1);
                                tag=1;
                            }
//                            p_tmp=p4->p_u-p4->p_l;
//                            if(p2->p_u>p_tmp)
//                            {
//                                *p11+=p4->p_l;
//                                p2->p_u-=p_tmp;
//                            }
//                            else
//                            {*p11+=p4->p_u-p2->p_u;tag=1;}
                        }
                        break;
                        case 1:
                        sum_p(p11,&p2->p,p4->p_u);
//                        *p11+=p4->p_u;
                        break;
                        case 2:
                        sum_p(p11,&p2->p,p4->p_l);
//                        *p11+=p4->p_l;
                    }
                }
                else if(!tag)
                {
                    sum_p(&p2->p_l,&err1,p4->p_l);
                    if(p2->p_l>p4->p_u)
                    sum_m(&p2->p_l,&err1,p4->p_u);
                    else tag=2;
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p_l>p_tmp)
//                    {p2->p_l-=p_tmp;}
//                    else{tag=2;}
                }
            }
        }
        if(p3!=p2)p3->next=0;else p2=0;
        if(!p2)continue;
        cnt1+=p2->num;
        if(tag)
        {
            p2->p_l=0.0;
            if(tag&1)
            {
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_u;}
                if(p2->x2)
                {p4=p2+p2->x2;p4->p=1.0/(1-p4->p_u);}
            }
            else
            {
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_l;}
                if(p2->x2)
                {p4=p2+p2->x2;p4->p=1.0/(1-p4->p_l);}
            }
        }else{p2->p_u=err1;}
    }
    printf("Size of iteration matrix = n + m = %u + %llu = %llu.\n",l2,cnt1,l2+cnt1);
    printf("Size of sort_edge = %llu.\n",cnt1);
    imc->x_vec=x_vec=(double*)malloc(l2*sizeof(double));//l2
    if(imc->sort_x)sort_x=imc->sort_x;
    else
    {
        imc->sort_x=sort_x=(double**)malloc(l2*sizeof(double*));
    }
    // x(0)=0, x(1)=b(for sort)
    p11=b_vec;p12=p11+l2;p13=x_vec;p14=sort_x;
    for(;p11!=p12;++p11,++p13,++p14)
    {*p13=*p11;*p14=p13;}
    // Sort x(1)
    qsort(sort_x,l2,sizeof(double*),cmp1);
    if(!permutation)
    permutation=(uint32_t*)malloc(l2*sizeof(uint32_t));
    for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
        *(*p14-x_vec+permutation)=cnt2;
    
    p16=p17=imc->sort_edge=sort_edge=(OUT_EDGE**)malloc(cnt1*sizeof(OUT_EDGE*));
    // assign probability to edges, x(1)=(I-D)^{-1}b <= (I-D-L)^{-1}b
    for(p7=decode_min,p13=x_vec;p7!=p8;++p7,++p13)
    {
        p2=p4=*(out_pos+*p7);
        if(!p2)continue;
        for(;p4->next;++p17)
        {p4+=p4->next;*p17=p4;}
        qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
        if(p2->p_l==0.0)
        {
            p16=p17;
            if(p2->x2)
            {
                p4=p2+p2->x2;*p13*=p4->p;
                err1=p2->p*p4->p;*p13+=err1;
            }
            continue;
        }
        for(p_tmp1=p2->p_l,err1=p2->p_u,tag=0;p16!=p17;++p16)
        {
            p4=*p16;
            if(tag)p4->p=p4->p_l;
            else
            {
                sum_p(&p_tmp1,&err1,p4->p_l);
                if(p_tmp1>p4->p_u)
                {
                    p4->p=p4->p_u;
                    sum_m(&p_tmp1,&err1,p4->p_u);
                }
                else{p4->p=p_tmp1;tag=2;}
//                p_tmp=p4->p_u-p4->p_l;
//                if(p2->p>p_tmp)
//                {
//                    p4->p=p4->p_u;
//                    p2->p-=p_tmp;
//                }
//                else{p4->p=p4->p_l+p2->p;tag=2;}
            }
        }
        if(p2->x2)
        {
            p4=p2+p2->x2;
            p4->p=1.0/(1-p4->p);
            *p13*=p4->p;
            err1=p2->p*p4->p;*p13+=err1;
        }
    }
    end_t=clock();
    printf("Time used to build data structure for iterative method = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    
    // MARK: Solve (I-D-L)x = Ux + b
    start_t=clock();
    printf("Solve (I-D-L)x = Ux + b:\n");
    
    p13=x_vec;
    for(p12=p13+l2;p13!=p12;++p13)
    *p13=1.0;
    
    for(cnt3=0,j=1;;++j)
    {
        for(i=1;i<=ITERATION_BOUND;++i)
        {
            p7=decode_min;p11=b_vec;
            p16=p17=sort_edge;
            p13=x_vec;
            err_max=0.0;
            for(;p7!=p8;++p7,++p11,++p12,++p13)
            {
                x_current=*p13;
                p2=p4=*(out_pos+*p7);
                if(!p4){*p13=*p11;continue;}
                if(p2->x2)
                {
                    p3=p2+p2->x2;
                    *p13=p4->p;err1=0.0;p17=p16+p4->num;
                    for(;p16!=p17;++p16)
                        if(*p16!=p3)
                        {
                            p_tmp=*(x_vec+(*p16)->x2)*(*p16)->p;
                            sum_p(p13,&err1,p_tmp);
                        }
                    sum_p(p13,&err1,*p11);
                    *p13*=p3->p;err1*=p3->p;*p13+=err1;
                    
//                    p3=p2+p2->x2;
//                    *p13=0;p17=p16+p4->num;
//                    for(;p16!=p17;++p16)
//                        if(*p16!=p3)*p13+=*(x_vec+(*p16)->x2)*(*p16)->p;
//                    *p13+=*p11;*p13*=p3->p;
                }
                else
                {
                    *p13=p4->p;err1=0.0;p17=p16+p4->num;
                    for(;p16!=p17;++p16)
                    {
                        p_tmp=*(x_vec+(*p16)->x2)*(*p16)->p;
                        sum_p(p13,&err1,p_tmp);
                    }
                    sum_p(p13,&err1,*p11);
                    
//                    *p13=0;p17=p16+p4->num;
//                    for(;p16!=p17;++p16)
//                    *p13+=*(x_vec+(*p16)->x2)*(*p16)->p;
//                    *p13+=*p11;
                }
                
                if(x_current+10*MACHINE_EPSILON<*p13)printf("Unexpected, not monotone decreasing: node[%u]: x_current: %.17e difference: %.3e.\n",*p7,x_current,(*p13-x_current)/MACHINE_EPSILON);
                
                if(*p13>x_current)*p13=x_current;
                
                err_current=fabs(*p13-x_current);
                if(err_current>err_max)err_max=err_current;
            }
            if(i==1)printf("Error_max after shift = %.17e.\t",err_max);
            if(err_max<=EPSILON)break;
        }
        printf("%u th iteration: ",j);
        if(i<=ITERATION_BOUND)printf("# of iterations: %u.",i);
        else printf("# of iterations exceeds ITERATION_BOUND %u.",ITERATION_BOUND);
        printf("\t err_max = %.17e.\n",err_max);
        cnt3+=i;
        if(i>ITERATION_BOUND)--cnt3;
        for(p14=sort_x,p15=p14+l2,p11=*p14,++p14;p14!=p15;++p14)
        {
            p12=*p14;
//            if(*p11<=*p12+MACHINE_EPSILON)p11=p12;
            if(*p11<=*p12)p11=p12;
            else break;
        }
        printf("\t%u\n",(uint32_t)(p14-sort_x));
        if(p14==p15)
        {
            if(i>ITERATION_BOUND){printf("Order doesn't change but needs more iterations.\n");continue;}
            else break;
        }
            
        qsort(sort_x,l2,sizeof(double*),cmp1);
        for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
            *(*p14-x_vec+permutation)=cnt2;
        // assign probability to edges
        p16=p17=sort_edge;
        for(p7=decode_min;p7!=p8;++p7)
        {
            p2=*(out_pos+*p7);
            if(!p2)continue;
            if(p2->p_l==0.0)
            {p16=p17+=p2->num;continue;}
            for(p18=p17+p2->num,p3=*p17,++p17;p17!=p18;++p17)
            {
                p4=*p17;
                if(*(permutation+p3->x2)<*(permutation+p4->x2))p3=p4;
                else break;
            }
            if(p17==p18){p16=p18;continue;}
            else p17=p18;
            qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
            for(p_tmp1=p2->p_l,err1=p2->p_u,tag=0;p16!=p17;++p16)
            {
                p4=*p16;
                if(tag)p4->p=p4->p_l;
                else
                {
                    sum_p(&p_tmp1,&err1,p4->p_l);
                    if(p_tmp1>p4->p_u)
                    {
                        p4->p=p4->p_u;
                        sum_m(&p_tmp1,&err1,p4->p_u);
                    }
                    else{p4->p=p_tmp1;tag=2;}
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p>p_tmp)
//                    {
//                        p4->p=p4->p_u;
//                        p2->p-=p_tmp;
//                    }
//                    else{p4->p=p4->p_l+p2->p;tag=2;}
                }
            }
            if(p2->x2)
            {p4=p2+p2->x2;p4->p=1.0/(1-p4->p);}
        }
    }
    
    printf("# of outer loop iterations :%u\n",j);
    printf("# of total loop iterations :%u\n",cnt3);
    
    for(p11=b_vec,p12=p11+l2,p13=x_vec;p11!=p12;++p11,++p13)
        *p11=*p13;
    head->x_vec_Gauss_Seidel_min=b_vec;
    imc->b_vec=0;
    free(x_vec);imc->x_vec=0;
    free(sort_edge);imc->sort_edge=0;
    
//    free(out_pos);imc->out_pos=0;
//    free(imc->out_edge);imc->out_edge=0;
//    free(decode1);head->decode1=0;
//    free(b_vec);imc->b_vec=0;
    end_t=clock();
    printf("Time used to solve (I-D-L)x = Ux + b = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("Time used to solve quantitative minimum reachability using Gauss Seidel method = %.4f\n",
           (double)(end_t-start_t0)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void solve_quantitative_min_reachability_power_GS_method(HEAD *head)
{
    IMC *imc;
    uint32_t n0,l2,cnt2,cnt3;
    uint32_t i,j;
    uint64_t cnt1;
    OUT_EDGE **out_pos,**sort_edge,*p2,*p3,*p4,**p16,**p17,**p18;
    uint32_t *encode_min,*decode_min,*p5,*p6,*p7,*p8;
    double err1,err2,p_tmp,p_tmp1,*x_vec,*b_vec,*p11,*p12,*p13,*x_current,*x_next,*x_tmp,x_crt,err_current,err_max = 0.0,**sort_x,**p14,**p15;
    BOOL *flag,*p9,tag;
    clock_t start_t0,start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    out_pos=imc->out_pos;
    flag=head->flag_min;
    n0=imc->n;
    l2=head->l2_min;
    
    printf("Solve quantitative minimum reachability using power-GS method:\n");
    
    // MARK: build data structure for iterative method
    start_t0=start_t=clock();
    printf("Build data structure for iterative method:\n");
    if(!l2)
    {
        printf("All states have trivial probability 0 or 1, so no quantitative minimum reachability needs to be solved.\n");
        return;
    }
    // Encode and decode
    if(head->encode_min)
    {
        encode_min=head->encode_min;
        decode_min=head->decode_min;
        p8=decode_min+l2;
    }
    else
    {
        head->encode_min=encode_min=imc->queue;imc->queue=0;
        head->decode_min=decode_min=(uint32_t*)malloc(l2*sizeof(uint32_t));
        p5=encode_min;p7=decode_min;p9=flag;
        for(p6=p5+n0;p5!=p6;++p5,++p9)
            if(*p9==2)
            {
                *p5=(uint32_t)(p7-decode_min);
                *p7=(uint32_t)(p5-encode_min);++p7;
            }
            else *p5=n0;
    }
    // Compute sum_l and sum_u
    for(p7=decode_min,p8=p7+l2;p7!=p8;++p7)
    {
        p2=p4=*(out_pos+*p7);
        for(p2->p=p2->p_l=p2->p_u=err1=err2=0.0;p4->next;)
        {
            p4+=p4->next;
            sum_p(&p2->p_l,&err1,p4->p_l);
            sum_p(&p2->p_u,&err2,p4->p_u);
//            p2->p_l+=p4->p_l;
//            p2->p_u+=p4->p_u;
        }
        // Sterbenz's lemma
        p_tmp=p2->p_l;p2->p_l=1.0;
        sum_m(&p2->p_l,&p2->p,p_tmp);
        sum_m(&p2->p_l,&p2->p,err1);
        
        sum_m(&p2->p_u,&err2,1.0);
        p2->p_u+=err2;
//        p2->p_l=1.0-p2->p_l;p2->p_u-=1.0;
    }
    // Set up (I-D-L)x = Ux + b
    p11=imc->b_vec=b_vec=(double*)calloc(l2,sizeof(double));
    for(p7=decode_min,cnt1=0;p7!=p8;++p7,++p11)
    {
        p2=p3=p4=*(out_pos+*p7);
        err1=p2->p;
        err2=p2->p=0.0;
        for(p2->x2=p2->num=tag=0;p4->next;)
        {
            p4+=p4->next;
            p9=flag+p4->x2;
            if(*p9==2)
            {
                p3=p4;++p2->num;
                if(*p7==p4->x2)p2->x2=(uint32_t)(p4-p2);
                p4->x2=*(encode_min+p4->x2);
            }
            else
            {
                p3->next+=p4->next;
                if(*p9&1)// label == 1 || 3
                {
                    switch(tag)
                    {
                        case 0:
                        {
                            p_tmp=p2->p_u;p_tmp1=err2;
                            sum_p(&p2->p_u,&err2,p4->p_l);
                            if(p2->p_u>p4->p_u)
                            {
                                sum_p(p11,&p2->p,p4->p_l);
                                sum_m(&p2->p_u,&err2,p4->p_u);
                            }
                            else
                            {
                                sum_p(p11,&p2->p,p4->p_u);
                                sum_m(p11,&p2->p,p_tmp);
                                sum_m(p11,&p2->p,p_tmp1);
                                tag=1;
                            }
//                            p_tmp=p4->p_u-p4->p_l;
//                            if(p2->p_u>p_tmp)
//                            {
//                                *p11+=p4->p_l;
//                                p2->p_u-=p_tmp;
//                            }
//                            else
//                            {*p11+=p4->p_u-p2->p_u;tag=1;}
                        }
                            break;
                            case 1:
                            sum_p(p11,&p2->p,p4->p_u);
    //                        *p11+=p4->p_u;
                            break;
                            case 2:
                            sum_p(p11,&p2->p,p4->p_l);
    //                        *p11+=p4->p_l;
                    }
                }
                else if(!tag)
                {
                    sum_p(&p2->p_l,&err1,p4->p_l);
                    if(p2->p_l>p4->p_u)
                    sum_m(&p2->p_l,&err1,p4->p_u);
                    else tag=2;
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p_l>p_tmp)
//                    {p2->p_l-=p_tmp;}
//                    else{tag=2;}
                }
            }
        }
        if(p3!=p2)p3->next=0;else p2=0;
        if(!p2)continue;
        cnt1+=p2->num;
        if(tag)
        {
            p2->p_l=0.0;
            if(tag&1)
            {
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_u;}
                if(p2->x2)
                {p4=p2+p2->x2;p4->p=1.0/(1-p4->p_u);}
            }
            else
            {
                for(p4=p2;p4->next;)
                {p4+=p4->next;p4->p=p4->p_l;}
                if(p2->x2)
                {p4=p2+p2->x2;p4->p=1.0/(1-p4->p_l);}
            }
        }else{p2->p_u=err1;}
    }
    printf("Size of iteration matrix = n + m = %u + %llu = %llu.\n",l2,cnt1,l2+cnt1);
    printf("Size of sort_edge = %llu.\n",cnt1);
    imc->x_vec=x_vec=(double*)malloc((l2<<1)*sizeof(double));//l2*2
    if(imc->sort_x)sort_x=imc->sort_x;
    else
    {
        imc->sort_x=sort_x=(double**)malloc(l2*sizeof(double*));
    }
    // x(0)=0, x(1)=b(for sort)
    p11=b_vec;p12=p11+l2;p13=x_vec;p14=sort_x;
    for(;p11!=p12;++p11,++p13,++p14)
    {*p13=*p11;*p14=p13;}
    // Sort x(1)
    qsort(sort_x,l2,sizeof(double*),cmp1);
    if(!permutation)
    permutation=(uint32_t*)malloc(l2*sizeof(uint32_t));
    for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
        *(*p14-x_vec+permutation)=cnt2;
    
    p16=p17=imc->sort_edge=sort_edge=(OUT_EDGE**)malloc(cnt1*sizeof(OUT_EDGE*));
    // assign probability to edges, x(1)=(I-D)^{-1}b <= (I-D-L)^{-1}b
    for(p7=decode_min,p13=x_vec;p7!=p8;++p7,++p13)
    {
        p2=p4=*(out_pos+*p7);
        if(!p2)continue;
        for(;p4->next;++p17)
        {p4+=p4->next;*p17=p4;}
        qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
        if(p2->p_l==0.0)
        {
            p16=p17;
            if(p2->x2)
            {
                p4=p2+p2->x2;*p13*=p4->p;
                err1=p2->p*p4->p;*p13+=err1;
            }
            continue;
        }
        for(p_tmp1=p2->p_l,err1=p2->p_u,tag=0;p16!=p17;++p16)
        {
            p4=*p16;
            if(tag)p4->p=p4->p_l;
            else
            {
                sum_p(&p_tmp1,&err1,p4->p_l);
                if(p_tmp1>p4->p_u)
                {
                    p4->p=p4->p_u;
                    sum_m(&p_tmp1,&err1,p4->p_u);
                }
                else{p4->p=p_tmp1;tag=2;}
//                p_tmp=p4->p_u-p4->p_l;
//                if(p2->p>p_tmp)
//                {
//                    p4->p=p4->p_u;
//                    p2->p-=p_tmp;
//                }
//                else{p4->p=p4->p_l+p2->p;tag=2;}
            }
        }
        if(p2->x2)
        {
            p4=p2+p2->x2;
            p4->p=1.0/(1-p4->p);
            *p13*=p4->p;
            err1=p2->p*p4->p;*p13+=err1;
        }
    }
    end_t=clock();
    printf("Time used to build data structure for iterative method = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    
    // MARK: Solve (I-D-L)x = Ux + b
    start_t=clock();
    printf("Solve (I-D-L)x = Ux + b:\n");
    
    p13=x_vec;
    for(p12=p13+l2;p13!=p12;++p13)
    *p13=1.0;
    
    for(cnt3=0,j=1;;++j)
    {
        for(i=1;i<=ITERATION_BOUND1;++i)
        {
            p7=decode_min;p11=b_vec;
            p16=p17=sort_edge;
            p13=x_vec;
            err_max=0.0;
            for(;p7!=p8;++p7,++p11,++p12,++p13)
            {
                x_crt=*p13;
                p2=p4=*(out_pos+*p7);
                if(!p4){*p13=*p11;continue;}
                if(p2->x2)
                {
                    p3=p2+p2->x2;
                    *p13=p4->p;err1=0.0;p17=p16+p4->num;
                    for(;p16!=p17;++p16)
                        if(*p16!=p3)
                        {
                            p_tmp=*(x_vec+(*p16)->x2)*(*p16)->p;
                            sum_p(p13,&err1,p_tmp);
                        }
                    sum_p(p13,&err1,*p11);
                    *p13*=p3->p;err1*=p3->p;*p13+=err1;
                    
//                    p3=p2+p2->x2;
//                    *p13=0;p17=p16+p4->num;
//                    for(;p16!=p17;++p16)
//                        if(*p16!=p3)*p13+=*(x_vec+(*p16)->x2)*(*p16)->p;
//                    *p13+=*p11;*p13*=p3->p;
                }
                else
                {
                    *p13=p4->p;err1=0.0;p17=p16+p4->num;
                    for(;p16!=p17;++p16)
                    {
                        p_tmp=*(x_vec+(*p16)->x2)*(*p16)->p;
                        sum_p(p13,&err1,p_tmp);
                    }
                    sum_p(p13,&err1,*p11);
                    
//                    *p13=0;p17=p16+p4->num;
//                    for(;p16!=p17;++p16)
//                    *p13+=*(x_vec+(*p16)->x2)*(*p16)->p;
//                    *p13+=*p11;
                }
                
                if(x_crt+4*x_crt*MACHINE_EPSILON<*p13)printf("Unexpected, not monotone decreasing: node[%u]: x_current: %.17e difference: %.3e.\n",*p7,x_crt,(*p13-x_crt)/MACHINE_EPSILON);
                
                if(*p13>x_crt)*p13=x_crt;
                
                err_current=fabs(*p13-x_crt);
                if(err_current>err_max)err_max=err_current;
            }
            if(i==1)printf("Error_max after shift = %.17e.\t",err_max);
            if(err_max<=EPSILON1)break;
            
        }
        printf("%u th iteration: ",j);
        if(i<=ITERATION_BOUND1)printf("# of iterations: %u.",i);
        else printf("# of iterations exceeds ITERATION_BOUND %u.",ITERATION_BOUND1);
        printf("\t err_max = %.17e.\n",err_max);
        cnt3+=i;
        if(i>ITERATION_BOUND1)--cnt3;
        for(p14=sort_x,p15=p14+l2,p11=*p14,++p14;p14!=p15;++p14)
        {
            p12=*p14;
//            if(*p11<=*p12+MACHINE_EPSILON)p11=p12;
            if(*p11<=*p12)p11=p12;
            else break;
        }
        printf("\t%u\n",(uint32_t)(p14-sort_x));
        if(p14==p15)
        {
            if(i>ITERATION_BOUND1){printf("Order doesn't change but needs more iterations.\n");continue;}
            else break;
        }
        if(err_max<=EPSILON1)break;
        qsort(sort_x,l2,sizeof(double*),cmp1);
        for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
            *(*p14-x_vec+permutation)=cnt2;
        // assign probability to edges
        p16=p17=sort_edge;
        for(p7=decode_min;p7!=p8;++p7)
        {
            p2=*(out_pos+*p7);
            if(!p2)continue;
            if(p2->p_l==0.0)
            {p16=p17+=p2->num;continue;}
            for(p18=p17+p2->num,p3=*p17,++p17;p17!=p18;++p17)
            {
                p4=*p17;
                if(*(permutation+p3->x2)<*(permutation+p4->x2))p3=p4;
                else break;
            }
            if(p17==p18){p16=p18;continue;}
            else p17=p18;
            qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
            for(p_tmp1=p2->p_l,err1=p2->p_u,tag=0;p16!=p17;++p16)
            {
                p4=*p16;
                if(tag)p4->p=p4->p_l;
                else
                {
                    sum_p(&p_tmp1,&err1,p4->p_l);
                    if(p_tmp1>p4->p_u)
                    {
                        p4->p=p4->p_u;
                        sum_m(&p_tmp1,&err1,p4->p_u);
                    }
                    else{p4->p=p_tmp1;tag=2;}
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p>p_tmp)
//                    {
//                        p4->p=p4->p_u;
//                        p2->p-=p_tmp;
//                    }
//                    else{p4->p=p4->p_l+p2->p;tag=2;}
                }
            }
            if(p2->x2)
            {p4=p2+p2->x2;p4->p=1.0/(1-p4->p);}
        }
    }
    
    printf("# of outer loop iterations :%u\n",j);
    printf("# of total loop iterations :%u\n",cnt3);
    
    end_t=clock();
    printf("Time used to solve (I-D-L)x = Ux + b = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    
    // MARK: Solve x = Ax + b
    start_t=clock();
    printf("Solve x = Ax + b:\n");
    qsort(sort_x,l2,sizeof(double*),cmp1);
    for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
        *(*p14-x_vec+permutation)=cnt2;
    // assign probability to edges
    p16=p17=sort_edge;
    for(p7=decode_min;p7!=p8;++p7)
    {
        p2=*(out_pos+*p7);
        if(!p2)continue;
        if(p2->p_l==0.0)
        {
            p16=p17+=p2->num;
            if(p2->x2)
            {
                p4=p2+p2->x2;
                if(p4->p==1.0/(1-p4->p_l))p4->p=p4->p_l;
                else if(p4->p==1.0/(1-p4->p_u))p4->p=p4->p_u;
                else printf("Bug in 1.0/(1-p).\n");
            }
            continue;
        }
        p17=p16+p2->num;
        qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
        for(p_tmp1=p2->p_l,err1=p2->p_u,tag=0;p16!=p17;++p16)
        {
            p4=*p16;
            if(tag)p4->p=p4->p_l;
            else
            {
                sum_p(&p_tmp1,&err1,p4->p_l);
                if(p_tmp1>p4->p_u)
                {
                    p4->p=p4->p_u;
                    sum_m(&p_tmp1,&err1,p4->p_u);
                }
                else{p4->p=p_tmp1;tag=2;}
//                p_tmp=p4->p_u-p4->p_l;
//                if(p2->p>p_tmp)
//                {
//                    p4->p=p4->p_u;
//                    p2->p-=p_tmp;
//                }
//                else{p4->p=p4->p_l+p2->p;tag=2;}
            }
        }
    }
    x_current=x_vec;x_next=x_vec+l2;
    for(cnt3=0,j=1;;++j)
    {
        for(i=1;i<=ITERATION_BOUND2;++i)
        {
            p7=decode_min;p11=b_vec;
            p16=p17=sort_edge;
            p12=x_current;p13=x_next;
            err_max=0.0;
            for(;p7!=p8;++p7,++p11,++p12,++p13)
            {
                p4=*(out_pos+*p7);
                if(!p4){*p13=*p11;continue;}
                for(*p13=p4->p,err1=0.0,p17=p16+p4->num;p16!=p17;++p16)
                {
                    p_tmp=*(x_current+(*p16)->x2)*(*p16)->p;
                    sum_p(p13,&err1,p_tmp);
                }
                sum_p(p13,&err1,*p11);
                
//                for(*p13=0,p17=p16+p4->num;p16!=p17;++p16)
//                    *p13+=*(x_current+(*p16)->x2)*(*p16)->p;
//                *p13+=*p11;
                
                if(*p12+MACHINE_EPSILON<*p13)printf("Unexpected, not monotone decreasing: node[%u]: x_current: %.17e difference: %.3e.\n",*p7,*p12,(*p13-*p12)/MACHINE_EPSILON);
                
//                if(*p13>*p12)*p13=*p12;
                
                err_current=fabs(*p13-*p12);
                if(err_current>err_max)err_max=err_current;
            }
            //swap x_current and x_next
            x_tmp=x_current;
            x_current=x_next;
            x_next=x_tmp;
            if(i==1)printf("Error_max after shift = %.17e.\t",err_max);
            if(err_max<=EPSILON2)break;
        }
        printf("%u th iteration: ",j);
        if(i<=ITERATION_BOUND2)printf("# of iterations: %u.",i);
        else printf("# of iterations exceeds ITERATION_BOUND %u.",ITERATION_BOUND2);
        printf("\t err_max = %.17e.",err_max);
        cnt3+=i;
        if(i>ITERATION_BOUND2)--cnt3;
        for(p14=sort_x,p15=p14+l2,p11=*p14,++p14;p14!=p15;++p14)
        {
            p12=*p14;
            if(*p11<=*p12)p11=p12;
            else break;
        }
        printf("\t%u\n",(uint32_t)(p14-sort_x));
        if(p14==p15)
        {
            if(i>ITERATION_BOUND2){printf("Order doesn't change but needs more iterations.\n");continue;}
            else break;
        }
        
        qsort(sort_x,l2,sizeof(double*),cmp1);
        for(p14=sort_x,cnt2=0;cnt2!=l2;++p14,++cnt2)
            *(*p14-x_vec+permutation)=cnt2;
        // assign probability to edges
        p16=p17=sort_edge;
        for(p7=decode_min;p7!=p8;++p7)
        {
            p2=*(out_pos+*p7);
            if(!p2)continue;
            if(p2->p_l==0.0)
            {p16=p17+=p2->num;continue;}
            for(p18=p17+p2->num,p3=*p17,++p17;p17!=p18;++p17)
            {
                p4=*p17;
                if(*(permutation+p3->x2)<*(permutation+p4->x2))p3=p4;
                else break;
            }
            if(p17==p18){p16=p18;continue;}
            else p17=p18;
            qsort(p16,p2->num,sizeof(OUT_EDGE*),cmp2);
            for(p_tmp1=p2->p_l,err1=p2->p_u,tag=0;p16!=p17;++p16)
            {
                p4=*p16;
                if(tag)p4->p=p4->p_l;
                else
                {
                    sum_p(&p_tmp1,&err1,p4->p_l);
                    if(p_tmp1>p4->p_u)
                    {
                        p4->p=p4->p_u;
                        sum_m(&p_tmp1,&err1,p4->p_u);
                    }
                    else{p4->p=p_tmp1;tag=2;}
//                    p_tmp=p4->p_u-p4->p_l;
//                    if(p2->p>p_tmp)
//                    {
//                        p4->p=p4->p_u;
//                        p2->p-=p_tmp;
//                    }
//                    else{p4->p=p4->p_l+p2->p;tag=2;}
                }
            }
        }
    }
    
    printf("# of outer loop iterations :%u\n",j);
    printf("# of total loop iterations :%u\n",cnt3);
    
    for(p11=b_vec,p12=p11+l2,p13=x_current;p11!=p12;++p11,++p13)
        *p11=*p13;
    head->x_vec_power_min=b_vec;
    imc->b_vec=0;
    free(x_vec);imc->x_vec=0;
    free(sort_edge);imc->sort_edge=0;
    
//    free(out_pos);imc->out_pos=0;
//    free(imc->out_edge);imc->out_edge=0;
//    free(decode1);head->decode1=0;
//    free(b_vec);imc->b_vec=0;
    
    end_t=clock();
    printf("Time used to solve x = Ax + b = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("Time used to solve quantitative minimum reachability using power-GS method = %.4f\n",
           (double)(end_t-start_t0)/CLOCKS_PER_SEC);
    printf("********\n\n");
}

void print(HEAD *head)
{
    IMC *imc;
    uint32_t l2;
    double *x_vec,*p11,*p12;
    FILE *fout;
    char buffer[40];
    clock_t start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    
    start_t=clock();
    
    if(head->x_vec_power_max)
    {
        x_vec=head->x_vec_power_max;
        l2=head->l2_max;
        printf("Write satisfaction probability for maximum quantitative reachability power method.\n");
        sprintf(buffer,"quan_max_power%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(p11=x_vec,p12=p11+l2;p11!=p12;++p11)
            fprintf(fout,"%.17e\n",*p11);
        fclose(fout);
    }
    
    if(head->x_vec_Jacobi_max)
    {
        x_vec=head->x_vec_Jacobi_max;
        l2=head->l2_max;
        printf("Write satisfaction probability for maximum quantitative reachability Jacobi method.\n");
        sprintf(buffer,"quan_max_Jacobi%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(p11=x_vec,p12=p11+l2;p11!=p12;++p11)
            fprintf(fout,"%.17e\n",*p11);
        fclose(fout);
    }
    
    if(head->x_vec_Gauss_Seidel_max)
    {
        x_vec=head->x_vec_Gauss_Seidel_max;
        l2=head->l2_max;
        printf("Write satisfaction probability for maximum quantitative reachability Gauss Seidel method.\n");
        sprintf(buffer,"quan_max_Gauss_Seidel%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(p11=x_vec,p12=p11+l2;p11!=p12;++p11)
            fprintf(fout,"%.17e\n",*p11);
        fclose(fout);
    }
    
    if(head->x_vec_power_min)
    {
        x_vec=head->x_vec_power_min;
        l2=head->l2_min;
        printf("Write satisfaction probability for minimum quantitative reachability power method.\n");
        sprintf(buffer,"quan_min_power%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(p11=x_vec,p12=p11+l2;p11!=p12;++p11)
            fprintf(fout,"%.17e\n",*p11);
        fclose(fout);
    }
    
    if(head->x_vec_Jacobi_min)
    {
        x_vec=head->x_vec_Jacobi_min;
        l2=head->l2_min;
        printf("Write satisfaction probability for minimum quantitative reachability Jacobi method.\n");
        sprintf(buffer,"quan_min_Jacobi%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(p11=x_vec,p12=p11+l2;p11!=p12;++p11)
            fprintf(fout,"%.17e\n",*p11);
        fclose(fout);
    }
    if(head->x_vec_Gauss_Seidel_min)
    {
        x_vec=head->x_vec_Gauss_Seidel_min;
        l2=head->l2_min;
        printf("Write satisfaction probability for minimum quantitative reachability Gauss Seidel method.\n");
        sprintf(buffer,"quan_min_Gauss_Seidel%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(p11=x_vec,p12=p11+l2;p11!=p12;++p11)
            fprintf(fout,"%.17e\n",*p11);
        fclose(fout);
    }
    
    end_t=clock();
    printf("Time used to write quantitative satisfaction probability =  %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
}

void print_index(HEAD *head)
{
    IMC *imc;
    uint32_t n0,*p5,cnt1;
    double *x_vec;
    BOOL *p9;
    FILE *fout;
    char buffer[40];
    clock_t start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    n0=imc->n;
    
    start_t=clock();
    
    if(head->x_vec_power_max)
    {
        x_vec=head->x_vec_power_max;
        p5=head->encode_max;
        p9=head->flag_max;
        
        
        printf("Write satisfaction probability for maximum quantitative reachability power method.\n");
        sprintf(buffer,"quan_max_power_index%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(cnt1=0;cnt1!=n0;++cnt1,++p9,++p5)
        {
            fprintf(fout,"%u\t\t",cnt1);
            if(!*p9)fprintf(fout,"0.0\n");
            else if(*p9&1)// label==1 || 3
                fprintf(fout,"1.0\n");
            else fprintf(fout,"%.15lf\n",*(x_vec+*p5));
        }
        fclose(fout);
    }
    
    if(head->x_vec_Jacobi_max)
    {
        x_vec=head->x_vec_Jacobi_max;
        p5=head->encode_max;
        p9=head->flag_max;
        
        
        printf("Write satisfaction probability for maximum quantitative reachability Jacobi method.\n");
        sprintf(buffer,"quan_max_Jacobi_index%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(cnt1=0;cnt1!=n0;++cnt1,++p9,++p5)
        {
            fprintf(fout,"%u\t\t",cnt1);
            if(!*p9)fprintf(fout,"0.0\n");
            else if(*p9&1)// label==1 || 3
                fprintf(fout,"1.0\n");
            else fprintf(fout,"%.15lf\n",*(x_vec+*p5));
        }
        fclose(fout);
    }
    
    if(head->x_vec_Gauss_Seidel_max)
    {
        x_vec=head->x_vec_Gauss_Seidel_max;
        p5=head->encode_max;
        p9=head->flag_max;
        
        
        printf("Write satisfaction probability for maximum quantitative reachability Gauss Seidel method.\n");
        sprintf(buffer,"quan_max_Gauss_Seidel_index%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(cnt1=0;cnt1!=n0;++cnt1,++p9,++p5)
        {
            fprintf(fout,"%u\t\t",cnt1);
            if(!*p9)fprintf(fout,"0.0\n");
            else if(*p9&1)// label==1 || 3
                fprintf(fout,"1.0\n");
            else fprintf(fout,"%.15lf\n",*(x_vec+*p5));
        }
        fclose(fout);
    }
    
    if(head->x_vec_power_min)
    {
        x_vec=head->x_vec_power_min;
        p5=head->encode_min;
        p9=head->flag_min;
        
        
        printf("Write satisfaction probability for minimum quantitative reachability power method.\n");
        sprintf(buffer,"quan_min_power_index%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(cnt1=0;cnt1!=n0;++cnt1,++p9,++p5)
        {
            fprintf(fout,"%u\t\t",cnt1);
            if(!*p9)fprintf(fout,"0.0\n");
            else if(*p9&1)// label==1 || 3
                fprintf(fout,"1.0\n");
            else fprintf(fout,"%.15lf\n",*(x_vec+*p5));
        }
        fclose(fout);
    }
    
    if(head->x_vec_Jacobi_min)
    {
        x_vec=head->x_vec_Jacobi_min;
        p5=head->encode_min;
        p9=head->flag_min;
        printf("Write satisfaction probability for minimum quantitative reachability Jacobi method.\n");
        sprintf(buffer,"quan_min_Jacobi_index%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(cnt1=0;cnt1!=n0;++cnt1,++p9,++p5)
        {
            fprintf(fout,"%u\t\t",cnt1);
            if(!*p9)fprintf(fout,"0.0\n");
            else if(*p9&1)// label==1 || 3
                fprintf(fout,"1.0\n");
            else fprintf(fout,"%.15lf\n",*(x_vec+*p5));
        }
        fclose(fout);
    }
    if(head->x_vec_Gauss_Seidel_min)
    {
        x_vec=head->x_vec_Gauss_Seidel_min;
        p5=head->encode_min;
        p9=head->flag_min;
        
        
        printf("Write satisfaction probability for minimum quantitative reachability Gauss Seidel method.\n");
        sprintf(buffer,"quan_min_Gauss_Seidel_index%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(cnt1=0;cnt1!=n0;++cnt1,++p9,++p5)
        {
            fprintf(fout,"%u\t\t",cnt1);
            if(!*p9)fprintf(fout,"0.0\n");
            else if(*p9&1)// label==1 || 3
                fprintf(fout,"1.0\n");
            else fprintf(fout,"%.15lf\n",*(x_vec+*p5));
        }
        fclose(fout);
    }
    
    end_t=clock();
    printf("Time used to write quantitative satisfaction probability =  %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
}

void print_index_permutation(HEAD *head)
{
    IMC *imc;
    uint32_t n0,l2,*p5,cnt1;
    double *x_vec;
    BOOL *p9;
    FILE *fout;
    char buffer[40];
    clock_t start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    n0=imc->n;
    
    start_t=clock();
    
    if(head->x_vec_power_max)
    {
        x_vec=head->x_vec_power_max;
        p5=head->encode_max;
        p9=head->flag_max;
        l2=head->l2_max;
        
        printf("Write satisfaction probability for maximum quantitative reachability power method.\n");
        sprintf(buffer,"quan_max_power_index%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(cnt1=0;cnt1!=n0;++cnt1,++p9,++p5)
        {
            fprintf(fout,"%u\t\t",cnt1);
            if(!*p9)fprintf(fout,"0.0\n");
            else if(*p9&1)// label==1 || 3
                fprintf(fout,"1.0\n");
            else fprintf(fout,"%.17e\n",*(x_vec+*p5));
        }
        for(cnt1=0;cnt1!=l2;++cnt1)
            fprintf(fout,"%u\n",*(permutation+cnt1));
        fclose(fout);
        head->x_vec_power_max=0;
    }
    
    if(head->x_vec_Jacobi_max)
    {
        x_vec=head->x_vec_Jacobi_max;
        p5=head->encode_max;
        p9=head->flag_max;
        l2=head->l2_max;
        
        printf("Write satisfaction probability for maximum quantitative reachability Jacobi method.\n");
        sprintf(buffer,"quan_max_Jacobi_index%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(cnt1=0;cnt1!=n0;++cnt1,++p9,++p5)
        {
            fprintf(fout,"%u\t\t",cnt1);
            if(!*p9)fprintf(fout,"0.0\n");
            else if(*p9&1)// label==1 || 3
                fprintf(fout,"1.0\n");
            else fprintf(fout,"%.17e\n",*(x_vec+*p5));
        }
        for(cnt1=0;cnt1!=l2;++cnt1)
            fprintf(fout,"%u\n",*(permutation+cnt1));
        fclose(fout);
        head->x_vec_Jacobi_max=0;
    }
    
    if(head->x_vec_Gauss_Seidel_max)
    {
        x_vec=head->x_vec_Gauss_Seidel_max;
        p5=head->encode_max;
        p9=head->flag_max;
        l2=head->l2_max;
        
        printf("Write satisfaction probability for maximum quantitative reachability Gauss Seidel method.\n");
        sprintf(buffer,"quan_max_Gauss_Seidel_index%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(cnt1=0;cnt1!=n0;++cnt1,++p9,++p5)
        {
            fprintf(fout,"%u\t\t",cnt1);
            if(!*p9)fprintf(fout,"0.0\n");
            else if(*p9&1)// label==1 || 3
                fprintf(fout,"1.0\n");
            else fprintf(fout,"%.17e\n",*(x_vec+*p5));
        }
        for(cnt1=0;cnt1!=l2;++cnt1)
            fprintf(fout,"%u\n",*(permutation+cnt1));
        fclose(fout);
        head->x_vec_Gauss_Seidel_max=0;
    }
    
    if(head->x_vec_power_min)
    {
        x_vec=head->x_vec_power_min;
        p5=head->encode_min;
        p9=head->flag_min;
        l2=head->l2_min;
        
        printf("Write satisfaction probability for minimum quantitative reachability power method.\n");
        sprintf(buffer,"quan_min_power_index%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(cnt1=0;cnt1!=n0;++cnt1,++p9,++p5)
        {
            fprintf(fout,"%u\t\t",cnt1);
            if(!*p9)fprintf(fout,"0.0\n");
            else if(*p9&1)// label==1 || 3
                fprintf(fout,"1.0\n");
            else fprintf(fout,"%.17e\n",*(x_vec+*p5));
        }
        for(cnt1=0;cnt1!=l2;++cnt1)
            fprintf(fout,"%u\n",*(permutation+cnt1));
        fclose(fout);
        head->x_vec_power_min=0;
    }
    
    if(head->x_vec_Jacobi_min)
    {
        x_vec=head->x_vec_Jacobi_min;
        p5=head->encode_min;
        p9=head->flag_min;
        l2=head->l2_min;
        
        printf("Write satisfaction probability for minimum quantitative reachability Jacobi method.\n");
        sprintf(buffer,"quan_min_Jacobi_index%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(cnt1=0;cnt1!=n0;++cnt1,++p9,++p5)
        {
            fprintf(fout,"%u\t\t",cnt1);
            if(!*p9)fprintf(fout,"0.0\n");
            else if(*p9&1)// label==1 || 3
                fprintf(fout,"1.0\n");
            else fprintf(fout,"%.17e\n",*(x_vec+*p5));
        }
        for(cnt1=0;cnt1!=l2;++cnt1)
            fprintf(fout,"%u\n",*(permutation+cnt1));
        fclose(fout);
        head->x_vec_Jacobi_min=0;
    }
    if(head->x_vec_Gauss_Seidel_min)
    {
        x_vec=head->x_vec_Gauss_Seidel_min;
        p5=head->encode_min;
        p9=head->flag_min;
        l2=head->l2_min;
        
        printf("Write satisfaction probability for minimum quantitative reachability Gauss Seidel method.\n");
        sprintf(buffer,"quan_min_Gauss_Seidel_index%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(cnt1=0;cnt1!=n0;++cnt1,++p9,++p5)
        {
            fprintf(fout,"%u\t\t",cnt1);
            if(!*p9)fprintf(fout,"0.0\n");
            else if(*p9&1)// label==1 || 3
                fprintf(fout,"1.0\n");
            else fprintf(fout,"%.17e\n",*(x_vec+*p5));
        }
        for(cnt1=0;cnt1!=l2;++cnt1)
            fprintf(fout,"%u\n",*(permutation+cnt1));
        fclose(fout);
        head->x_vec_Gauss_Seidel_min=0;
    }
    
    end_t=clock();
    printf("Time used to write quantitative satisfaction probability =  %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
}


void compare_error(HEAD *head)
{
    IMC *imc;
    uint32_t n0,cnt1,i,j,x;
    double *x_vec,*p1,*p2,err_current,err_max;
    FILE *fin,*fout;
    char buffer[40];
    clock_t start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    n0=imc->n;
    
    start_t=clock();
    printf("Input compare file:\n");
    
    sprintf(buffer,"compare_in.txt");
    printf("Read file to compare:\n");
    
    x_vec=malloc((n0<<1)*sizeof(double));
    
    fin=fopen(buffer,"rb");
    
    for(i=0,cnt1=n0<<1,p1=x_vec;i!=cnt1;++i,++p1)
        fscanf(fin,"%u%lf",&x,p1);
    
    fclose(fin);
    
    sprintf(buffer,"compare_out.txt");
    fout=fopen(buffer,"wb");
    
    for(i=j=0,p1=x_vec,p2=p1+n0,err_max=0.0;i!=n0;++i,++p1,++p2)
    {
        err_current=fabs(*p1-*p2);
        if(err_current>err_max)err_max=err_current;
        if(err_current>EPSILON)
        {
            ++j;
            fprintf(fout,"%u\t\t%.17e\t\t%.17e\t\t%.17e\n",i,*p1,*p1-*p2,(*p1-*p2)/(*p1));
        }
    }
    fprintf(fout,"--------\n");
    fprintf(fout,"error_max = %.15e\n",err_max);
    fprintf(fout,"# of errors exceed EPSILON %.15e = %u\n",EPSILON,j);
    fclose(fout);
    
    
    end_t=clock();
    printf("Time used to write compare file =  %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
}

void compare_error_permutation(HEAD *head)
{
    IMC *imc;
    uint32_t n0,cnt1,i,j,x,*cmp_permutation,*p3,*p4,l2;
    double *x_vec,*p1,*p2,err_current,err_max;
    FILE *fin,*fout;
    char buffer[40];
    clock_t start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    n0=imc->n;
    l2=imc->l2;
    
    start_t=clock();
    printf("Input compare file:\n");
    
    sprintf(buffer,"compare_in.txt");
    printf("Read file to compare:\n");
    
    x_vec=malloc((n0<<1)*sizeof(double));
    cmp_permutation=malloc((l2<<1)*sizeof(uint32_t));
    
    fin=fopen(buffer,"rb");
    
    for(i=0,p1=x_vec,p3=cmp_permutation;i!=2;++i)
    {
        for(cnt1=0;cnt1!=n0;++cnt1,++p1)
            fscanf(fin,"%u%lf",&x,p1);
        for(cnt1=0;cnt1!=l2;++cnt1,++p3)
            fscanf(fin,"%u",p3);
    }
    
    fclose(fin);
    
    sprintf(buffer,"compare_out.txt");
    fout=fopen(buffer,"wb");
    
    for(i=j=0,p1=x_vec,p2=p1+n0,err_max=0.0;i!=n0;++i,++p1,++p2)
    {
        err_current=fabs(*p1-*p2);
        if(err_current>err_max)err_max=err_current;
        if(err_current>EPSILON)
        {
            ++j;
            fprintf(fout,"%u\t\t%.15e\t\t%.15e\n",i,*p1,(*p1-*p2)/MACHINE_EPSILON);
        }
    }
    fprintf(fout,"--------\n");
    fprintf(fout,"error_max/MACHINE_EPSILON = %.15e\n",err_max/MACHINE_EPSILON);
    fprintf(fout,"# of errors > EPSILON %.15e = %u\n",EPSILON,j);
    fprintf(fout,"--------\n");
    for(cnt1=j=0,p3=cmp_permutation,p4=p3+l2;cnt1!=l2;++cnt1,++p3,++p4)
    {
        if(*p3!=*p4)
        {
            ++j;
            fprintf(fout,"%u:\t%u\t%u\n",cnt1,*p3,*p4);
        }
    }
    fprintf(fout,"# of permutations that do not match: %u\n",j);
    fclose(fout);
    end_t=clock();
    printf("Time used to write compare file =  %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
}

void monotone(HEAD *head)
{
    IMC *imc;
    uint32_t n0,cnt1,i,j,x;
    double *x_vec,*p1,*p2;
    FILE *fin,*fout;
    char buffer[40];
    clock_t start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    n0=imc->n;
    
    start_t=clock();
    printf("Input compare file:\n");
    
    sprintf(buffer,"compare_in.txt");
    printf("Read file to compare:\n");
    
    x_vec=malloc((n0<<1)*sizeof(double));
    
    fin=fopen(buffer,"rb");
    
    for(i=0,cnt1=n0,p1=x_vec;i!=cnt1;++i,++p1)
        fscanf(fin,"%u%lf",&x,p1);
    
    fclose(fin);
    
    sprintf(buffer,"compare_out.txt");
    fout=fopen(buffer,"wb");
    
    for(i=1,j=0,p1=x_vec,p2=p1+1;i!=n0;++i,++p1,++p2)
    {
        //max
        if(*p2>*p1+EPSILON)
        {
            ++j;
            fprintf(fout,"%u\t\t%.15e\t\t%.15e\n",i,*p2,*p2-*p1);
        }

        
        
        
    }
    fprintf(fout,"--------\n");
    fprintf(fout,"# of terms not monotone = %u\n",j);
    fclose(fout);
    
    
    end_t=clock();
    printf("Time used to write compare file =  %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
}

void print_compare(HEAD *head)
{
    IMC *imc;
    uint32_t l2;
    double *p11,*p12,*p13,*p14;
    FILE *fout;
    char buffer[40];
    clock_t start_t,end_t;
    
    if(!head->imc.n)return;
    imc=&head->imc;
    
    start_t=clock();
    
    if(head->x_vec_power_max&&head->x_vec_Jacobi_max&&head->x_vec_Gauss_Seidel_max)
    {
        p11=head->x_vec_power_max;
        p12=head->x_vec_Jacobi_max;
        p13=head->x_vec_Gauss_Seidel_max;
        l2=head->l2_max;
        printf("Write satisfaction probability comparison for maximum quantitative reachability.\n");
        sprintf(buffer,"quan_max_cmp%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(p14=p11+l2;p11!=p14;++p11,++p12,++p13)
            fprintf(fout,"%.6f\t%.6e\t%.6e\n",*p11,*p12-*p11,*p13-*p12);
        fclose(fout);
    }
    
    if(head->x_vec_power_min&&head->x_vec_Jacobi_min&&head->x_vec_Gauss_Seidel_min)
    {
        p11=head->x_vec_power_min;
        p12=head->x_vec_Jacobi_min;
        p13=head->x_vec_Gauss_Seidel_min;
        l2=head->l2_min;
        printf("Write satisfaction probability comparison for minimum quantitative reachability.\n");
        sprintf(buffer,"quan_min_cmp%hu_%hu.txt",
                head->imc_num,head->label_num);
        
        fout=fopen(buffer,"wb");
        for(p14=p11+l2;p11!=p14;++p11,++p12,++p13)
            fprintf(fout,"%.6f\t%.6e\t%.6e\n",*p11,*p12-*p11,*p13-*p12);
        fclose(fout);
    }
    
    end_t=clock();
    printf("Time used to write quantitative satisfaction probability comparison =  %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    
    
}



void free_memory(HEAD *head)
{
    IMC *imc;
    clock_t start_t,end_t;
    
    imc=&head->imc;
    
    // MARK: free memory
    start_t=clock();
    printf("Free memory:\n");
    
    if(permutation)free(permutation);permutation=0;
    
    /// Free head
    if(head->encode_max)free(head->encode_max);head->encode_max=0;
    if(head->decode_max)free(head->decode_max);head->decode_max=0;
    if(head->encode_min)free(head->encode_min);head->encode_min=0;
    if(head->decode_min)free(head->decode_min);head->decode_min=0;
    head->l2_max=head->l2_min=0;
    if(head->x_vec_power_max)free(head->x_vec_power_max);head->x_vec_power_max=0;
    if(head->x_vec_Jacobi_max)free(head->x_vec_Jacobi_max);head->x_vec_Jacobi_max=0;
    if(head->x_vec_Gauss_Seidel_max)free(head->x_vec_Gauss_Seidel_max);head->x_vec_Gauss_Seidel_max=0;
    if(head->x_vec_power_min)free(head->x_vec_power_min);head->x_vec_power_min=0;
    if(head->x_vec_Jacobi_min)free(head->x_vec_Jacobi_min);head->x_vec_Jacobi_min=0;
    if(head->x_vec_Gauss_Seidel_min)free(head->x_vec_Gauss_Seidel_min);head->x_vec_Gauss_Seidel_min=0;
    if(head->flag_max)free(head->flag_max);head->flag_max=0;
    if(head->flag_min)free(head->flag_min);head->flag_min=0;
    
    ///Free imc
    if(imc->out_pos)free(imc->out_pos);imc->out_pos=0;
    if(imc->out_pos_reset)free(imc->out_pos_reset);imc->out_pos_reset=0;
    if(imc->sort_edge)free(imc->sort_edge);imc->sort_edge=0;
    if(imc->out_edge)free(imc->out_edge);imc->out_edge=0;
    if(imc->in_deg)free(imc->in_deg);imc->in_deg=0;
    if(imc->in_pos)free(imc->in_pos);imc->in_pos=0;
    if(imc->in_edge)free(imc->in_edge);imc->in_edge=0;
    if(imc->x_vec)free(imc->x_vec);imc->x_vec=0;
    if(imc->b_vec)free(imc->b_vec);imc->b_vec=0;
    if(imc->sort_x)free(imc->sort_x);imc->sort_x=0;
    if(imc->queue)free(imc->queue);imc->queue=0;
    imc->n=0;
    end_t=clock();
    printf("Time used to  = %.4f\n",
           (double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("********\n\n");
}










int main(int argc, const char * argv[]) {
    HEAD head,*p = &head;
    clock_t start_t,end_t;
    
    p->imc_num = 86; p->label_num = 1;
    
    start_t=clock();
    initialization(p);
    input_imc_post(p);
    input_label_and_post2pre(p);
//    solve_qualitative_max_reachability(p);
//
//
//    compare_error(p);
//    compare_error_permutation(p);
//    monotone(p);
    
//    solve_quantitative_max_reachability_power_method(p);
//    print_index_permutation(p);
//    reset_imc(p,2);
    
//    solve_quantitative_max_reachability_Jacobi_method(p);
//    print_index_permutation(p);
//    reset_imc(p,2);
    
//    solve_quantitative_max_reachability_Gauss_Seidel_method(p);
//    print_index_permutation(p);
//    reset_imc(p,1);
    
//    solve_quantitative_max_reachability_power_GS_method(p);
//    print_index_permutation(p);
    
//    solve_quantitative_max_reachability_power_method_modified(p);
//    print_index_permutation(p);
    
//    solve_quantitative_max_reachability_power_method_aggressive(p);
//    print_index_permutation(p);
    
//    reset_imc(p,1);
//
    solve_qualitative_min_reachability(p);
//    compare_error(p);
//    compare_error_permutation(p);
    
    solve_quantitative_min_reachability_power_method(p);
    print_index_permutation(p);
//    reset_imc(p,4);
//    solve_quantitative_min_reachability_Jacobi_method(p);
//    print_index_permutation(p);
//    reset_imc(p,4);
//    solve_quantitative_min_reachability_Gauss_Seidel_method(p);
//    print_index_permutation(p);
//    reset_imc(p,4);
//    solve_quantitative_min_reachability_power_GS_method(p);
//        print_index_permutation(p);
    
//    print(p);
    
//    print_index(p);
//    print_index_permutation(p);
    
//    print_compare(p);
    
    free_memory(p);
    end_t=clock();
    printf("Time used to solve imc reachability = %.4f\n\n",(double)(end_t-start_t)/CLOCKS_PER_SEC);
    printf("********\n\n");
    
//    float a;
//    double b;
//    a=0.123456789;
//    b=0.123456789123456789;
//    printf("%.10f\n",a);
//
//    // insert code here...
//    printf("Hello, World!\n");
    
    
    return 0;
}

