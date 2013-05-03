/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

#include <iostream>
#include <string>

#include "common.h"
#include <assert.h>
#include "Context.h"
#include "misc.h"
#include "PrivateKey.h"
#include "PublicKey.h"
#include "Vote.h"

int main()
{
    mpz_t p;
    mpz_t p_minus_1;
    mpz_t q;
    mpz_t g;
    mpz_t h;
    mpz_t f;
    mpz_t G;
    mpz_t H;
    mpz_t t0;
    mpz_t s1;
    mpz_t c1;
    mpz_t y0;
    mpz_t z0;
    mpz_t g_to_the_s1;
    mpz_t G_to_the_minus_c1;
    mpz_t y1;
    mpz_t h_to_the_s1;
    mpz_t H_over_f;
    mpz_t H_over_f_to_the_c1;
    mpz_t H_over_f_to_the_minus_c1;
    mpz_t z1;
    mpz_t c;
    mpz_t c0;
    mpz_t s0;
    mpz_t r;
    mpz_t c0_times_r;
    mpz_t z1_times_H_over_f_to_the_c1;
    mpz_t g_to_the_s0;
    mpz_t h_to_the_s0;
    mpz_t c0_plus_c1;
    mpz_t G_to_the_c1;
    mpz_t H_to_the_c0;
    mpz_t G_to_the_c0;
    mpz_t y0_times_G_to_the_c0;
    mpz_t z0_times_H_to_the_c0;
    mpz_t y1_times_G_to_the_c1;

    mpz_init(p);
    mpz_init(p_minus_1);
    mpz_init(q);
    mpz_init(g);
    mpz_init(h);
    mpz_init(f);
    mpz_init(G);
    mpz_init(H);
    mpz_init(t0);
    mpz_init(s1);
    mpz_init(c1);
    mpz_init(y0);
    mpz_init(z0);
    mpz_init(g_to_the_s1);
    mpz_init(G_to_the_minus_c1);
    mpz_init(y1);
    mpz_init(h_to_the_s1);
    mpz_init(H_over_f);
    mpz_init(H_over_f_to_the_c1);
    mpz_init(H_over_f_to_the_minus_c1);
    mpz_init(z1);
    mpz_init(c);
    mpz_init(c0);
    mpz_init(s0);
    mpz_init(r);
    mpz_init(c0_times_r);
    mpz_init(g_to_the_s0);
    mpz_init(h_to_the_s0);
    mpz_init(c0_plus_c1);
    mpz_init(G_to_the_c1);
    mpz_init(H_to_the_c0);
    mpz_init(G_to_the_c0);
    mpz_init(y0_times_G_to_the_c0);
    mpz_init(z0_times_H_to_the_c0);
    mpz_init(y1_times_G_to_the_c1);
    mpz_init(H_over_f_to_the_c1);
    mpz_init(z1_times_H_over_f_to_the_c1);

    std::string myVote = "0";
    adder::Vote vote;

    adder::Context context(true);
    adder::PublicKey pub_key(&context);
    adder::PrivateKey priv_key;

    pub_key.make_partial_key(8);
    priv_key = pub_key.gen_key_pair();

    std::cout << "Public key: " << pub_key.str() << std::endl;

    /* p */
    mpz_set_str(p, pub_key.get_p_str().c_str(), 0);

    /* q */
    mpz_sub_ui(p_minus_1, p, 1);
    mpz_divexact_ui(q, p_minus_1, 2);

    /* g */
    mpz_set_str(g, pub_key.get_g_str().c_str(), 0);

    /* h */
    mpz_set_str(h, pub_key.get_h_str().c_str(), 0);

    /* f */
    mpz_set_str(f, pub_key.get_f_str().c_str(), 0);

    //    vote = pub_key.encrypt(myVote);

    /* G */
    mpz_set_str(G, vote.get_G_str().c_str(), 0);

    /* H */
    mpz_set_str(H, vote.get_H_str().c_str(), 0);

    /* r */
    mpz_set_str(r, vote.get_r_str().c_str(), 0);

    /* t0 <-R [0, q] */
    mpz_urandomm(t0, *(context.get_state()), q);

    std::cout << "t0: " << mpz_get_str(0, 10, t0) << std::endl;

    /* s1, c1 <-R [0, q] */
    mpz_urandomm(s1, *(context.get_state()), q);
    mpz_urandomm(c1, *(context.get_state()), q);

    /* y0 = g^t0 */
    mpz_powm(y0, g, t0, p);

    /* z0 = h^t0 */
    mpz_powm(z0, h, t0, p);

    /* g^s1 */
    mpz_powm(g_to_the_s1, g, s1, p);

    /* G^c1 */
    mpz_powm(G_to_the_c1, G, c1, p);

    /* G^-c1 */
    mpz_invert(G_to_the_minus_c1, G_to_the_c1, p);

    /* y1 = g^s1 * G^-c1 */
    mpz_mul(y1, g_to_the_s1, G_to_the_minus_c1);
    mpz_mod(y1, y1, p);

    /* h^s1 */
    mpz_powm(h_to_the_s1, h, s1, p);        

    /* H / f */
    mpz_set_str(H_over_f, adder::Zq_divide(mpz_get_str(0, 10, H), mpz_get_str(0, 10, f),mpz_get_str(0, 10, p)).c_str(), 0);

    mpz_powm(H_over_f_to_the_c1, H_over_f, c1, p);

    /* (H / f)^-c1 */
    mpz_invert(H_over_f_to_the_minus_c1, H_over_f_to_the_c1, p);

    /* z1 = h^s1 * (H / f)^-c1 */
    mpz_mul(z1, h_to_the_s1, H_over_f_to_the_minus_c1);
    mpz_mod(z1, z1, p);

    /* c <-R [0, q] */
    mpz_urandomm(c, *(context.get_state()), q);

    /* c0 = c - c1 */
    mpz_set_str(c0,
		adder::Zq_sub(mpz_get_str(0, 10, c),
			      mpz_get_str(0, 10, c1),
			      mpz_get_str(0, 10, q)).c_str(), 0);

    std::cout << "c0: " << mpz_get_str(0, 10, c0) << std::endl;
    std::cout << "c1: " << mpz_get_str(0, 10, c1) << std::endl;
    std::cout << "c: " << mpz_get_str(0, 10, c) << std::endl;
    std::cout << "q: " << mpz_get_str(0, 10, q) << std::endl;

    /* c0 * r */
    mpz_mul(c0_times_r, c0, r);
    mpz_mod(c0_times_r, c0_times_r, q);

    std::cout << "c0 * r: " << mpz_get_str(0, 10, c0_times_r) << std::endl;

    /* s0 = t0 + c0 * r */
    mpz_add(s0, t0, c0_times_r);
    mpz_mod(s0, s0, q);

    std::cout << "g: " << mpz_get_str(0, 10, g) << std::endl;
    std::cout << "s0: " << mpz_get_str(0, 10, s0) << std::endl;

    /* g^s0 */
    mpz_powm(g_to_the_s0, g, s0, p);

    /* G^c0 */
    mpz_powm(G_to_the_c0, G, c0, p);

    /* y0 * G^c0 */
    mpz_mul(y0_times_G_to_the_c0, y0, G_to_the_c0);
    mpz_mod(y0_times_G_to_the_c0, y0_times_G_to_the_c0, p);

    /* h^s0 */
    mpz_powm(h_to_the_s0, h, s0, p);

    /* H^c0 */
    mpz_powm(H_to_the_c0, H, c0, p);

    /* z0 * H^c0 */
    mpz_mul(z0_times_H_to_the_c0, z0, H_to_the_c0);
    mpz_mod(z0_times_H_to_the_c0, z0_times_H_to_the_c0, p);

    /* y1 * G^c1 */
    mpz_mul(y1_times_G_to_the_c1, y1, G_to_the_c1);
    mpz_mod(y1_times_G_to_the_c1, y1_times_G_to_the_c1, p);

    /* (H / f)^c1 */
    mpz_powm(H_over_f_to_the_c1, H_over_f, c1, p);

    /* z1 * (H / f)^c1 */
    mpz_mul(z1_times_H_over_f_to_the_c1, z1, H_over_f_to_the_c1);
    mpz_mod(z1_times_H_over_f_to_the_c1, z1_times_H_over_f_to_the_c1, p);

    /* c0_plus_c1 */
    mpz_add(c0_plus_c1, c0, c1);
    mpz_mod(c0_plus_c1, c0_plus_c1, q);

    std::cout << "p: " << mpz_get_str(0, 10, p) << std::endl;
    std::cout << "y0: " << mpz_get_str(0, 10, y0) << std::endl;
    std::cout << "G: " << mpz_get_str(0, 10, G) << std::endl;
    std::cout << "g^s0: " << mpz_get_str(0, 10, g_to_the_s0) << std::endl;
    std::cout << "y0 * G^c0: " << mpz_get_str(0, 10, y0_times_G_to_the_c0) << std::endl;
    std::cout << "r: " << mpz_get_str(0, 10, r) << std::endl;
    std::cout << "h: " << mpz_get_str(0, 10, h) << std::endl;

    assert(!mpz_cmp(c, c0_plus_c1));
    assert(!mpz_cmp(g_to_the_s0, y0_times_G_to_the_c0));
    assert(!mpz_cmp(h_to_the_s0, z0_times_H_to_the_c0));
    assert(!mpz_cmp(g_to_the_s1, y1_times_G_to_the_c1));
    assert(!mpz_cmp(h_to_the_s1, z1_times_H_over_f_to_the_c1));

    mpz_clear(p);
    mpz_clear(p_minus_1);
    mpz_clear(q);
    mpz_clear(g);
    mpz_clear(h);
    mpz_clear(f);
    mpz_clear(G);
    mpz_clear(H);
    mpz_clear(t0);
    mpz_clear(s1);
    mpz_clear(c1);
    mpz_clear(y0);
    mpz_clear(z0);
    mpz_clear(g_to_the_s1);
    mpz_clear(G_to_the_minus_c1);
    mpz_clear(y1);
    mpz_clear(h_to_the_s1);
    mpz_clear(H_over_f);
    mpz_clear(H_over_f_to_the_c1);
    mpz_clear(H_over_f_to_the_minus_c1);
    mpz_clear(z1);
    mpz_clear(c);
    mpz_clear(c0);
    mpz_clear(s0);
    mpz_clear(r);
    mpz_clear(c0_times_r);
    mpz_clear(g_to_the_s0);
    mpz_clear(h_to_the_s0);
    mpz_clear(c0_plus_c1);
    mpz_clear(G_to_the_c1);
    mpz_clear(H_to_the_c0);
    mpz_clear(G_to_the_c0);
    mpz_clear(y0_times_G_to_the_c0);
    mpz_clear(z0_times_H_to_the_c0);
    mpz_clear(y1_times_G_to_the_c1);
    mpz_clear(H_over_f_to_the_c1);
    mpz_clear(z1_times_H_over_f_to_the_c1);

    return 0;
}
