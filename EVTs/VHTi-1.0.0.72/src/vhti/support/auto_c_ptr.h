/*  */
/* This material is subject to the VoteHere Source Code Evaluation */
/* License Agreement ("Agreement").  Possession and/or use of this */
/* material indicates your acceptance of this Agreement in its entirety. */
/* Copies of the Agreement may be found at www.votehere.net. */
/*  */
/* Copyright 2004 VoteHere, Inc.  All Rights Reserved */
/*  */
/* You may not download this Software if you are located in any country */
/* (or are a national of a country) subject to a general U.S. or */
/* U.N. embargo or are deemed to be a terrorist country (i.e., Cuba, */
/* Iran, Iraq, Libya, North Korea, Sudan and Syria) by the United States */
/* (each a "Prohibited Country") or are otherwise denied export */
/* privileges from the United States or Canada ("Denied Person"). */
/* Further, you may not transfer or re-export the Software to any such */
/* country or Denied Person without a license or authorization from the */
/* U.S. government.  By downloading the Software, you represent and */
/* warrant that you are not a Denied Person, are not located in or a */
/* national of a Prohibited Country, and will not export or re-export to */
/* any Prohibited Country or Denied Party. */
#ifndef AUTO_C_PTR_H
#define AUTO_C_PTR_H

#ifdef __cplusplus

template <class _T, class free_T>
class auto_C_PTR
{
public:
   explicit auto_C_PTR<_T, free_T>(_T * t) : m_t(t) {}
   ~auto_C_PTR<_T, free_T>(void) 
   { 
      free();
   }
   typedef auto_C_PTR<_T, free_T> _this;
   _this & operator = (_T * t) 
   { 
      free(); 
      m_t = t; 
      return * this; 
   }
   operator _T * (void) 
   { 
      return m_t; 
   }
   _this * operator ->(void) const
   {
      return m_t;
   }
   _this & operator * (void) const
   {
      return * m_t;
   }
   bool operator != (const _T * t) const
   {
      return (m_t != t);
   }
   bool operator < (const _T * t) const
   {
      return (m_t < t);
   }
   bool operator <= (const _T * t) const
   {
      return (m_t <= t);
   }
   void free(void) 
   { 
      if (m_t) { 
         free_T::free(m_t); 
      } 
      m_t = NULL;
   }
private:
   _T * m_t;
};

// Example usage:

// class free_BN_CTX {
// public:
//    static free(BN_CTX * ctx)
//    {
//       BN_CTX_free(ctx);
//    }
// };
// typedef auto_C_PTR<BN_CTX, free_BN_CTX> auto_BN_CTX;


#endif
#endif
