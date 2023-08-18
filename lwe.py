#sage9.2 in Linux
"""
This program is final code to solve LWE problem,the main direction is LWE->BDD->uSVP.
Using Q-ary lattice transfer LWE problem to BDD problem,and transform BDD problem to uSVP problem by Kannan's Embedding method.
The key is optimize the BKZ alogrithm.First we decide to repeatly shuffle the order of rows of matrix to arise the BKZ successful 
rate which in function rndomBKZ(),but no much effert in high dimension. Later we found library of fpylll which conclude BKZ2.0 that 
faster than BKZ in sage,we called the function of fpylll in randomBKZ2().
However,BKZ2.0 also need lots of time in higher dimension,we eventually found g6k Sieve Kernel in github,called sieve kernel in randomBKZ3(),
which just faster than BKZ2.0 in high dimension like m=280.
Finally we found the program lwechallenge.py in g6k is the fastest way to solve LWE program.

: param m: dimension of vector
: param n: dimension of matrix
: param q: modulus
: param t: parameter of Kannan's Embedding
: param bs: the parameter block_size of BKZ2.0
: param ml: the parameter max_loop of BKZ2.0

"""
from sage.all import *
from fpylll import *
from fpylll.algorithms.bkz2 import BKZReduction as BKZ2
from g6k import *
import time
from g6k import Siever
from g6k.utils.stats import SieveTreeTracer
from g6k.algorithms.bkz import pump_n_jump_bkz_tour
from g6k.utils.stats import SieveTreeTracer
from g6k.algorithms.workout import workout
m = 160
n = 40
q = 256
t= 1
bs=20
ml=10

def readData(m,n):
    """
    read matrix A and read vector b 
    
    return list of A and b
    
    :param m:
    :param n:
    
    """
    #read b
    str1='worksrc/lwe'+str(m)+'-'+str(n)+'-b.txt'
    str2='worksrc/lwe'+str(m)+'-'+str(n)+'-A.txt'
    f = open(str1,'r').read()
    b_values= list(map(int,f.rstrip('\n').split('\n')))

    # read A.
    f = open(str2,'r')
    A_values = []
    for line in f.readlines():
        line = line.replace('\n','').split(' ')
        line = list(map(int,line))
        A_values.append(line)
    f.close()
    return b_values,A_values

def constructQaryLattices(m,n,q,A_values):
    """
    constrcut q-ary Lattice from matrix A  which is 
    
    [ In            0      ]
    [ A2*A1^(-1)  q*I(m-n) ]
    
    return  q-ary Lattice of A
    
    :param m: 
    :param n: 
    :param q: modulus
    :param A_values: list of matrix A
    
    
    """
    R=Zmod(q)
    P=list(identity_matrix(m))
    Av=matrix(ZZ,A_values)
    while(1):#Find invertible A1 by repeating lots of times 
        P1=P
        shuffle(P1)#m*n
        Pm=matrix(ZZ,P1)
        Am=Pm*Av
        print (Pm.inverse().nrows())

        A1 = matrix(R,n,n)
        for i in range(n):
            for j in range(n):
                A1[i,j]=Am[i,j]

        A2 = matrix(R,m-n,n)
        for i in range(m-n):
            for j in range(n):
                A2[i,j]=Am[i+n,j]

        if(A1.is_invertible()):
            print (1)
            AA=A2*A1.inverse()
            break
    A = matrix(ZZ,m,m)
    for i in range(n):
        A[i,i]=1
    for i in range(m-n):
        A[i+n,i+n]=q

    for i in range(m-n):
        for j in range(n):
            A[i+n,j]=AA[i][j]

    A=Pm.inverse()*A
    return A

def KannanEmbedding(m,n,A,bv,t):
    """
    construct matrix of Kannan's Embedding  which is 
    
    [ A   b ]
    [ 0   t ]
    
    return list of matrix of Kannan's Embedding
    
    :param m:
    :param n:
    :param A: list of q-ary matrix A     
    """
    l=[]
    for i in range(m):
        l.append(list(A[i])+[int(bv[i])])
    l.append([0]*m+[int(t)])
    return l

def randomBKZ(n,m,l):
    """
    using BKZ by repeating lots of times
    
    :param n:
    :param m:
    :param l:list of q-ary matrix A 
    """
    PP=list(identity_matrix(m+1))
    s=0
    Bt=matrix(ZZ,l).transpose()
    while(1):
        s=s+1
        PP1=PP
        shuffle(PP1)
        PPm=matrix(ZZ,PP1)
        Bt1=PPm*Bt   # Bt random rows
        e1  = Bt1.BKZ(block_size=bs)[0]
        print("%s:BKZ done")%s
        if e1.norm().n() < 256:
            break
    return e1

def randomBKZ2(n,m,l):
    """
    using BKZ2.0 from fpylll and repeating lots of times
    
    :param n:
    :param m:
    :param l:list of q-ary matrix A 
    """
    PP=list(identity_matrix(m+1))
    s=0
    Bt=matrix(ZZ,l).transpose()
    while True:
        s+=1
        shuffle(PP)
        PPm=matrix(ZZ,PP)
        M1=IntegerMatrix.from_matrix(list(PPm*Bt))
        bkz = BKZ2(M1) # just make a bkz2 object
        _= bkz(BKZ.EasyParam(bs, max_loops=ml, flags=BKZ.AUTO_ABORT|BKZ.MAX_LOOPS|BKZ.GH_BND))# start BKZ2
        e1 = M1[0]
        print(str(s)+":BKZ done")
        if e1.norm() < 256:
            break
        if s>=10:
            return False
    return e1

def randomBKZ3(n,m,l):#bkz
    '''
    using BKZ-seive from g6k and repeating lots of times
    
    :param n:
    :param m:
    :param l:list of q-ary matrix A 
    '''
    PP=list(identity_matrix(m+1))
    s=0
    Bt=matrix(ZZ,l).transpose()
    while True:
        s+=1
        shuffle(PP)
        PPm=matrix(ZZ,PP)
        M1=(IntegerMatrix.from_matrix(list(PPm*Bt)))
        g6k=Siever(M1) # make a sieve object
        tracer = SieveTreeTracer(g6k, root_label=("full-sieve", 50), start_clocks=True)#
        print("start to BKZ...")
        for b in (20,30,40,50,60,70):#using progressive block_size of BKZ
            pump_n_jump_bkz_tour(g6k, tracer, b, pump_params={"down_sieve": True})
            e1 = M1[0] 
            print(e1.norm()) 
            if e1.norm() < 256:
                print("BKZ done.")
                return e1
        if s>=10:
            return False
        print(str(s)+":BKZ done")
    
def checking(m,n,q,e1,A_values,b_values,t):
    """
    check the error vector
    
    :param m:
    :param n:
    :param q:modulus
    :param e1:the shortest vector from BKZ
    :param A_values: list of original matrix A
    :param b_values: list of orignal vector b
    :param t: parameter t from Kannan's Embedding
    """
    # check the answer.
    RR=Zmod(q)
    ee=vector(RR,e1[:-1])
    bb=vector(RR,b_values)
    if e1[-1] == -t: #-e
        ee=-ee
    elif e1[-1] == t:
        ee=ee
    res=bb-ee
    AA=matrix(RR,A_values)
    ss=AA.solve_right(res)
    print("Sercet Vector: {}".format(ss))
    print ("checking...")
    if AA*ss+ee == bb :
        print( "succeed.")
    return True


def main():
    (b_values,A_values)=readData(m,n)
    bv=vector(ZZ,b_values)
    start = time.process_time()
    while True:
        end0 = time.process_time()
        AA=constructQaryLattices(m,n,q,A_values)
        end1 = time.process_time()
        print (("matrix ok.time : %fs")%((end1-end0)))
        l=KannanEmbedding(m,n,AA,bv,t)
        e1=randomBKZ2(n,m,l)
        if e1 == False:
            continue
        print (("norm:{}".format(e1.norm())))
        print (e1)
        end2 = time.process_time()
        print (("time : %fs")%((end2-start)))
        if checking(m,n,q,list(e1),A_values,b_values,t):
            break

if __name__ == "__main__":
    main()