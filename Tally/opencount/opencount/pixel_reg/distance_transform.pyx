import numpy as np
cimport numpy as np
 
def dt1(np.ndarray[np.float_t,ndim=1] f):
    cdef int n = f.size
    cdef np.ndarray[np.float_t,ndim=1] D = np.zeros(n,dtype=np.float)
    cdef np.ndarray[np.int_t,ndim=1] R = np.zeros(n,dtype=np.int)

    cdef int k = 0
    cdef np.ndarray[np.int_t,ndim=1] v = np.zeros(n,dtype=np.int)
    cdef np.ndarray[np.float_t,ndim=1] z = np.zeros(n+1,dtype=np.float)

    z[0] = -np.inf
    z[1] = np.inf

    cdef np.int q
    cdef np.float_t s1
    cdef np.float_t fq
    cdef np.float_t fvk
    cdef np.float_t vk
    cdef np.float_t zk1
    cdef np.float dnm
    for q in range(1,n-1):
        fq = f[q]
        fvk = f[v[k]]
        vk = <float> v[k]
        dnm = 2 * q - 2 * vk
        s1 = fq/dnm + q**2/dnm - fvk/dnm - vk**2/dnm
        while s1 <= z[k]:
            k -= 1
            fvk = f[v[k]]
            vk = <float> v[k]
            dnm = 2 * q - 2 * vk
            s1 = fq/dnm + q**2/dnm - fvk/dnm - vk**2/dnm
        
        k += 1
        v[k] = q
        z[k] = s1
        z[k+1] = np.inf

    k = 1
    for q in range(n-1):
        zk1 = z[k+1]
        while zk1 < q:
            k += 1
            zk1 = z[k+1]
        vk = <float> v[k]
        fvk = f[v[k]]
        D[q] = q**2 -2*q*vk + vk**2 + fvk
        R[q] = <int> vk
        
    return (D,R)

def dt2(np.ndarray[np.float_t,ndim=2] I):
    cdef np.ndarray[np.float_t,ndim=2] res = np.zeros((I.shape[0],I.shape[1]),dtype=np.float)
    cdef np.ndarray[np.int_t,ndim=2] Rx = np.zeros((I.shape[0],I.shape[1]),dtype=np.int)
    cdef np.ndarray[np.int_t,ndim=2] Ry = np.zeros((I.shape[0],I.shape[1]),dtype=np.int)
    cdef int i
    cdef np.ndarray[np.float_t,ndim=1] D
    cdef np.ndarray[np.int_t,ndim=1] x
    cdef np.ndarray[np.int_t,ndim=1] y
    for i in range(I.shape[0]):
        (D,x) = dt1(I[i,:])
        res[i,:] = D
        Rx[i,:] = x

    for i in range(I.shape[1]):
        (D,y) = dt1(res[:,i])
        res[:,i] = D
        Ry[:,i] = y

    return (res,Rx,Ry)


