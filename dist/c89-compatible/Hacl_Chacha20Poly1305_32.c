/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "Hacl_Chacha20Poly1305_32.h"

static void
Hacl_Chacha20Poly1305_32_poly1305_padded_32(uint64_t *ctx, uint32_t len, uint8_t *text)
{
  uint32_t n1 = len / (uint32_t)16U;
  uint32_t r = len % (uint32_t)16U;
  uint8_t *blocks = text;
  uint8_t *rem1 = text + n1 * (uint32_t)16U;
  uint64_t *pre0 = ctx + (uint32_t)5U;
  uint64_t *acc0 = ctx;
  uint32_t nb = n1 * (uint32_t)16U / (uint32_t)16U;
  uint32_t rem2 = n1 * (uint32_t)16U % (uint32_t)16U;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < nb; i = i + (uint32_t)1U)
    {
      uint8_t *block = blocks + i * (uint32_t)16U;
      uint64_t e[5U] = { 0U };
      uint64_t u0 = load64_le(block);
      uint64_t lo = u0;
      uint64_t u = load64_le(block + (uint32_t)8U);
      uint64_t hi = u;
      uint64_t f0 = lo;
      uint64_t f1 = hi;
      uint64_t f010 = f0 & (uint64_t)0x3ffffffU;
      uint64_t f110 = f0 >> (uint32_t)26U & (uint64_t)0x3ffffffU;
      uint64_t f20 = f0 >> (uint32_t)52U | (f1 & (uint64_t)0x3fffU) << (uint32_t)12U;
      uint64_t f30 = f1 >> (uint32_t)14U & (uint64_t)0x3ffffffU;
      uint64_t f40 = f1 >> (uint32_t)40U;
      uint64_t f01 = f010;
      uint64_t f111 = f110;
      uint64_t f2 = f20;
      uint64_t f3 = f30;
      uint64_t f41 = f40;
      e[0U] = f01;
      e[1U] = f111;
      e[2U] = f2;
      e[3U] = f3;
      e[4U] = f41;
      {
        uint64_t b = (uint64_t)0x1000000U;
        uint64_t mask = b;
        uint64_t f4 = e[4U];
        e[4U] = f4 | mask;
        {
          uint64_t *r1 = pre0;
          uint64_t *r5 = pre0 + (uint32_t)5U;
          uint64_t r0 = r1[0U];
          uint64_t r11 = r1[1U];
          uint64_t r2 = r1[2U];
          uint64_t r3 = r1[3U];
          uint64_t r4 = r1[4U];
          uint64_t r51 = r5[1U];
          uint64_t r52 = r5[2U];
          uint64_t r53 = r5[3U];
          uint64_t r54 = r5[4U];
          uint64_t f10 = e[0U];
          uint64_t f11 = e[1U];
          uint64_t f12 = e[2U];
          uint64_t f13 = e[3U];
          uint64_t f14 = e[4U];
          uint64_t a0 = acc0[0U];
          uint64_t a1 = acc0[1U];
          uint64_t a2 = acc0[2U];
          uint64_t a3 = acc0[3U];
          uint64_t a4 = acc0[4U];
          uint64_t a01 = a0 + f10;
          uint64_t a11 = a1 + f11;
          uint64_t a21 = a2 + f12;
          uint64_t a31 = a3 + f13;
          uint64_t a41 = a4 + f14;
          uint64_t a02 = r0 * a01;
          uint64_t a12 = r11 * a01;
          uint64_t a22 = r2 * a01;
          uint64_t a32 = r3 * a01;
          uint64_t a42 = r4 * a01;
          uint64_t a03 = a02 + r54 * a11;
          uint64_t a13 = a12 + r0 * a11;
          uint64_t a23 = a22 + r11 * a11;
          uint64_t a33 = a32 + r2 * a11;
          uint64_t a43 = a42 + r3 * a11;
          uint64_t a04 = a03 + r53 * a21;
          uint64_t a14 = a13 + r54 * a21;
          uint64_t a24 = a23 + r0 * a21;
          uint64_t a34 = a33 + r11 * a21;
          uint64_t a44 = a43 + r2 * a21;
          uint64_t a05 = a04 + r52 * a31;
          uint64_t a15 = a14 + r53 * a31;
          uint64_t a25 = a24 + r54 * a31;
          uint64_t a35 = a34 + r0 * a31;
          uint64_t a45 = a44 + r11 * a31;
          uint64_t a06 = a05 + r51 * a41;
          uint64_t a16 = a15 + r52 * a41;
          uint64_t a26 = a25 + r53 * a41;
          uint64_t a36 = a35 + r54 * a41;
          uint64_t a46 = a45 + r0 * a41;
          uint64_t t0 = a06;
          uint64_t t1 = a16;
          uint64_t t2 = a26;
          uint64_t t3 = a36;
          uint64_t t4 = a46;
          uint64_t l = t0 + (uint64_t)0U;
          uint64_t tmp0 = l & (uint64_t)0x3ffffffU;
          uint64_t c01 = l >> (uint32_t)26U;
          uint64_t l0 = t1 + c01;
          uint64_t tmp1 = l0 & (uint64_t)0x3ffffffU;
          uint64_t c11 = l0 >> (uint32_t)26U;
          uint64_t l1 = t2 + c11;
          uint64_t tmp2 = l1 & (uint64_t)0x3ffffffU;
          uint64_t c21 = l1 >> (uint32_t)26U;
          uint64_t l2 = t3 + c21;
          uint64_t tmp3 = l2 & (uint64_t)0x3ffffffU;
          uint64_t c31 = l2 >> (uint32_t)26U;
          uint64_t l3 = t4 + c31;
          uint64_t tmp4 = l3 & (uint64_t)0x3ffffffU;
          uint64_t c4 = l3 >> (uint32_t)26U;
          uint64_t l4 = tmp0 + c4 * (uint64_t)5U;
          uint64_t tmp01 = l4 & (uint64_t)0x3ffffffU;
          uint64_t c5 = l4 >> (uint32_t)26U;
          uint64_t tmp11 = tmp1 + c5;
          uint64_t o0 = tmp01;
          uint64_t o1 = tmp11;
          uint64_t o2 = tmp2;
          uint64_t o3 = tmp3;
          uint64_t o4 = tmp4;
          acc0[0U] = o0;
          acc0[1U] = o1;
          acc0[2U] = o2;
          acc0[3U] = o3;
          acc0[4U] = o4;
        }
      }
    }
  }
  if (rem2 > (uint32_t)0U)
  {
    uint8_t *last1 = blocks + nb * (uint32_t)16U;
    uint64_t e[5U] = { 0U };
    uint8_t tmp[16U] = { 0U };
    memcpy(tmp, last1, rem2 * sizeof last1[0U]);
    {
      uint64_t u0 = load64_le(tmp);
      uint64_t lo = u0;
      uint64_t u = load64_le(tmp + (uint32_t)8U);
      uint64_t hi = u;
      uint64_t f0 = lo;
      uint64_t f1 = hi;
      uint64_t f010 = f0 & (uint64_t)0x3ffffffU;
      uint64_t f110 = f0 >> (uint32_t)26U & (uint64_t)0x3ffffffU;
      uint64_t f20 = f0 >> (uint32_t)52U | (f1 & (uint64_t)0x3fffU) << (uint32_t)12U;
      uint64_t f30 = f1 >> (uint32_t)14U & (uint64_t)0x3ffffffU;
      uint64_t f40 = f1 >> (uint32_t)40U;
      uint64_t f01 = f010;
      uint64_t f111 = f110;
      uint64_t f2 = f20;
      uint64_t f3 = f30;
      uint64_t f4 = f40;
      e[0U] = f01;
      e[1U] = f111;
      e[2U] = f2;
      e[3U] = f3;
      e[4U] = f4;
      {
        uint64_t b = (uint64_t)1U << rem2 * (uint32_t)8U % (uint32_t)26U;
        uint64_t mask = b;
        uint64_t fi = e[rem2 * (uint32_t)8U / (uint32_t)26U];
        e[rem2 * (uint32_t)8U / (uint32_t)26U] = fi | mask;
        {
          uint64_t *r1 = pre0;
          uint64_t *r5 = pre0 + (uint32_t)5U;
          uint64_t r0 = r1[0U];
          uint64_t r11 = r1[1U];
          uint64_t r2 = r1[2U];
          uint64_t r3 = r1[3U];
          uint64_t r4 = r1[4U];
          uint64_t r51 = r5[1U];
          uint64_t r52 = r5[2U];
          uint64_t r53 = r5[3U];
          uint64_t r54 = r5[4U];
          uint64_t f10 = e[0U];
          uint64_t f11 = e[1U];
          uint64_t f12 = e[2U];
          uint64_t f13 = e[3U];
          uint64_t f14 = e[4U];
          uint64_t a0 = acc0[0U];
          uint64_t a1 = acc0[1U];
          uint64_t a2 = acc0[2U];
          uint64_t a3 = acc0[3U];
          uint64_t a4 = acc0[4U];
          uint64_t a01 = a0 + f10;
          uint64_t a11 = a1 + f11;
          uint64_t a21 = a2 + f12;
          uint64_t a31 = a3 + f13;
          uint64_t a41 = a4 + f14;
          uint64_t a02 = r0 * a01;
          uint64_t a12 = r11 * a01;
          uint64_t a22 = r2 * a01;
          uint64_t a32 = r3 * a01;
          uint64_t a42 = r4 * a01;
          uint64_t a03 = a02 + r54 * a11;
          uint64_t a13 = a12 + r0 * a11;
          uint64_t a23 = a22 + r11 * a11;
          uint64_t a33 = a32 + r2 * a11;
          uint64_t a43 = a42 + r3 * a11;
          uint64_t a04 = a03 + r53 * a21;
          uint64_t a14 = a13 + r54 * a21;
          uint64_t a24 = a23 + r0 * a21;
          uint64_t a34 = a33 + r11 * a21;
          uint64_t a44 = a43 + r2 * a21;
          uint64_t a05 = a04 + r52 * a31;
          uint64_t a15 = a14 + r53 * a31;
          uint64_t a25 = a24 + r54 * a31;
          uint64_t a35 = a34 + r0 * a31;
          uint64_t a45 = a44 + r11 * a31;
          uint64_t a06 = a05 + r51 * a41;
          uint64_t a16 = a15 + r52 * a41;
          uint64_t a26 = a25 + r53 * a41;
          uint64_t a36 = a35 + r54 * a41;
          uint64_t a46 = a45 + r0 * a41;
          uint64_t t0 = a06;
          uint64_t t1 = a16;
          uint64_t t2 = a26;
          uint64_t t3 = a36;
          uint64_t t4 = a46;
          uint64_t l = t0 + (uint64_t)0U;
          uint64_t tmp0 = l & (uint64_t)0x3ffffffU;
          uint64_t c01 = l >> (uint32_t)26U;
          uint64_t l0 = t1 + c01;
          uint64_t tmp1 = l0 & (uint64_t)0x3ffffffU;
          uint64_t c11 = l0 >> (uint32_t)26U;
          uint64_t l1 = t2 + c11;
          uint64_t tmp2 = l1 & (uint64_t)0x3ffffffU;
          uint64_t c21 = l1 >> (uint32_t)26U;
          uint64_t l2 = t3 + c21;
          uint64_t tmp3 = l2 & (uint64_t)0x3ffffffU;
          uint64_t c31 = l2 >> (uint32_t)26U;
          uint64_t l3 = t4 + c31;
          uint64_t tmp4 = l3 & (uint64_t)0x3ffffffU;
          uint64_t c4 = l3 >> (uint32_t)26U;
          uint64_t l4 = tmp0 + c4 * (uint64_t)5U;
          uint64_t tmp01 = l4 & (uint64_t)0x3ffffffU;
          uint64_t c5 = l4 >> (uint32_t)26U;
          uint64_t tmp11 = tmp1 + c5;
          uint64_t o0 = tmp01;
          uint64_t o1 = tmp11;
          uint64_t o2 = tmp2;
          uint64_t o3 = tmp3;
          uint64_t o4 = tmp4;
          acc0[0U] = o0;
          acc0[1U] = o1;
          acc0[2U] = o2;
          acc0[3U] = o3;
          acc0[4U] = o4;
        }
      }
    }
  }
  {
    uint8_t tmp[16U] = { 0U };
    memcpy(tmp, rem1, r * sizeof rem1[0U]);
    if (r > (uint32_t)0U)
    {
      uint64_t *pre = ctx + (uint32_t)5U;
      uint64_t *acc = ctx;
      uint64_t e[5U] = { 0U };
      uint64_t u0 = load64_le(tmp);
      uint64_t lo = u0;
      uint64_t u = load64_le(tmp + (uint32_t)8U);
      uint64_t hi = u;
      uint64_t f0 = lo;
      uint64_t f1 = hi;
      uint64_t f010 = f0 & (uint64_t)0x3ffffffU;
      uint64_t f110 = f0 >> (uint32_t)26U & (uint64_t)0x3ffffffU;
      uint64_t f20 = f0 >> (uint32_t)52U | (f1 & (uint64_t)0x3fffU) << (uint32_t)12U;
      uint64_t f30 = f1 >> (uint32_t)14U & (uint64_t)0x3ffffffU;
      uint64_t f40 = f1 >> (uint32_t)40U;
      uint64_t f01 = f010;
      uint64_t f111 = f110;
      uint64_t f2 = f20;
      uint64_t f3 = f30;
      uint64_t f41 = f40;
      e[0U] = f01;
      e[1U] = f111;
      e[2U] = f2;
      e[3U] = f3;
      e[4U] = f41;
      {
        uint64_t b = (uint64_t)0x1000000U;
        uint64_t mask = b;
        uint64_t f4 = e[4U];
        e[4U] = f4 | mask;
        {
          uint64_t *r1 = pre;
          uint64_t *r5 = pre + (uint32_t)5U;
          uint64_t r0 = r1[0U];
          uint64_t r11 = r1[1U];
          uint64_t r2 = r1[2U];
          uint64_t r3 = r1[3U];
          uint64_t r4 = r1[4U];
          uint64_t r51 = r5[1U];
          uint64_t r52 = r5[2U];
          uint64_t r53 = r5[3U];
          uint64_t r54 = r5[4U];
          uint64_t f10 = e[0U];
          uint64_t f11 = e[1U];
          uint64_t f12 = e[2U];
          uint64_t f13 = e[3U];
          uint64_t f14 = e[4U];
          uint64_t a0 = acc[0U];
          uint64_t a1 = acc[1U];
          uint64_t a2 = acc[2U];
          uint64_t a3 = acc[3U];
          uint64_t a4 = acc[4U];
          uint64_t a01 = a0 + f10;
          uint64_t a11 = a1 + f11;
          uint64_t a21 = a2 + f12;
          uint64_t a31 = a3 + f13;
          uint64_t a41 = a4 + f14;
          uint64_t a02 = r0 * a01;
          uint64_t a12 = r11 * a01;
          uint64_t a22 = r2 * a01;
          uint64_t a32 = r3 * a01;
          uint64_t a42 = r4 * a01;
          uint64_t a03 = a02 + r54 * a11;
          uint64_t a13 = a12 + r0 * a11;
          uint64_t a23 = a22 + r11 * a11;
          uint64_t a33 = a32 + r2 * a11;
          uint64_t a43 = a42 + r3 * a11;
          uint64_t a04 = a03 + r53 * a21;
          uint64_t a14 = a13 + r54 * a21;
          uint64_t a24 = a23 + r0 * a21;
          uint64_t a34 = a33 + r11 * a21;
          uint64_t a44 = a43 + r2 * a21;
          uint64_t a05 = a04 + r52 * a31;
          uint64_t a15 = a14 + r53 * a31;
          uint64_t a25 = a24 + r54 * a31;
          uint64_t a35 = a34 + r0 * a31;
          uint64_t a45 = a44 + r11 * a31;
          uint64_t a06 = a05 + r51 * a41;
          uint64_t a16 = a15 + r52 * a41;
          uint64_t a26 = a25 + r53 * a41;
          uint64_t a36 = a35 + r54 * a41;
          uint64_t a46 = a45 + r0 * a41;
          uint64_t t0 = a06;
          uint64_t t1 = a16;
          uint64_t t2 = a26;
          uint64_t t3 = a36;
          uint64_t t4 = a46;
          uint64_t l = t0 + (uint64_t)0U;
          uint64_t tmp0 = l & (uint64_t)0x3ffffffU;
          uint64_t c01 = l >> (uint32_t)26U;
          uint64_t l0 = t1 + c01;
          uint64_t tmp1 = l0 & (uint64_t)0x3ffffffU;
          uint64_t c11 = l0 >> (uint32_t)26U;
          uint64_t l1 = t2 + c11;
          uint64_t tmp2 = l1 & (uint64_t)0x3ffffffU;
          uint64_t c21 = l1 >> (uint32_t)26U;
          uint64_t l2 = t3 + c21;
          uint64_t tmp3 = l2 & (uint64_t)0x3ffffffU;
          uint64_t c31 = l2 >> (uint32_t)26U;
          uint64_t l3 = t4 + c31;
          uint64_t tmp4 = l3 & (uint64_t)0x3ffffffU;
          uint64_t c4 = l3 >> (uint32_t)26U;
          uint64_t l4 = tmp0 + c4 * (uint64_t)5U;
          uint64_t tmp01 = l4 & (uint64_t)0x3ffffffU;
          uint64_t c5 = l4 >> (uint32_t)26U;
          uint64_t tmp11 = tmp1 + c5;
          uint64_t o0 = tmp01;
          uint64_t o1 = tmp11;
          uint64_t o2 = tmp2;
          uint64_t o3 = tmp3;
          uint64_t o4 = tmp4;
          acc[0U] = o0;
          acc[1U] = o1;
          acc[2U] = o2;
          acc[3U] = o3;
          acc[4U] = o4;
        }
      }
    }
  }
}

static void
Hacl_Chacha20Poly1305_32_poly1305_do_32(
  uint8_t *k,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t mlen,
  uint8_t *m,
  uint8_t *out
)
{
  uint64_t ctx[25U] = { 0U };
  uint8_t block[16U] = { 0U };
  uint64_t *pre;
  uint64_t *acc;
  Hacl_Poly1305_32_poly1305_init(ctx, k);
  Hacl_Chacha20Poly1305_32_poly1305_padded_32(ctx, aadlen, aad);
  Hacl_Chacha20Poly1305_32_poly1305_padded_32(ctx, mlen, m);
  store64_le(block, (uint64_t)aadlen);
  store64_le(block + (uint32_t)8U, (uint64_t)mlen);
  pre = ctx + (uint32_t)5U;
  acc = ctx;
  {
    uint64_t e[5U] = { 0U };
    uint64_t u0 = load64_le(block);
    uint64_t lo = u0;
    uint64_t u = load64_le(block + (uint32_t)8U);
    uint64_t hi = u;
    uint64_t f0 = lo;
    uint64_t f1 = hi;
    uint64_t f010 = f0 & (uint64_t)0x3ffffffU;
    uint64_t f110 = f0 >> (uint32_t)26U & (uint64_t)0x3ffffffU;
    uint64_t f20 = f0 >> (uint32_t)52U | (f1 & (uint64_t)0x3fffU) << (uint32_t)12U;
    uint64_t f30 = f1 >> (uint32_t)14U & (uint64_t)0x3ffffffU;
    uint64_t f40 = f1 >> (uint32_t)40U;
    uint64_t f01 = f010;
    uint64_t f111 = f110;
    uint64_t f2 = f20;
    uint64_t f3 = f30;
    uint64_t f41 = f40;
    uint64_t b;
    uint64_t mask;
    uint64_t f4;
    uint64_t *r;
    uint64_t *r5;
    uint64_t r0;
    uint64_t r1;
    uint64_t r2;
    uint64_t r3;
    uint64_t r4;
    uint64_t r51;
    uint64_t r52;
    uint64_t r53;
    uint64_t r54;
    uint64_t f10;
    uint64_t f11;
    uint64_t f12;
    uint64_t f13;
    uint64_t f14;
    uint64_t a0;
    uint64_t a1;
    uint64_t a2;
    uint64_t a3;
    uint64_t a4;
    uint64_t a01;
    uint64_t a11;
    uint64_t a21;
    uint64_t a31;
    uint64_t a41;
    uint64_t a02;
    uint64_t a12;
    uint64_t a22;
    uint64_t a32;
    uint64_t a42;
    uint64_t a03;
    uint64_t a13;
    uint64_t a23;
    uint64_t a33;
    uint64_t a43;
    uint64_t a04;
    uint64_t a14;
    uint64_t a24;
    uint64_t a34;
    uint64_t a44;
    uint64_t a05;
    uint64_t a15;
    uint64_t a25;
    uint64_t a35;
    uint64_t a45;
    uint64_t a06;
    uint64_t a16;
    uint64_t a26;
    uint64_t a36;
    uint64_t a46;
    uint64_t t0;
    uint64_t t1;
    uint64_t t2;
    uint64_t t3;
    uint64_t t4;
    uint64_t l0;
    uint64_t tmp0;
    uint64_t c01;
    uint64_t l1;
    uint64_t tmp1;
    uint64_t c11;
    uint64_t l2;
    uint64_t tmp2;
    uint64_t c21;
    uint64_t l3;
    uint64_t tmp3;
    uint64_t c31;
    uint64_t l4;
    uint64_t tmp4;
    uint64_t c4;
    uint64_t l;
    uint64_t tmp01;
    uint64_t c5;
    uint64_t tmp11;
    uint64_t o0;
    uint64_t o1;
    uint64_t o2;
    uint64_t o3;
    uint64_t o4;
    e[0U] = f01;
    e[1U] = f111;
    e[2U] = f2;
    e[3U] = f3;
    e[4U] = f41;
    b = (uint64_t)0x1000000U;
    mask = b;
    f4 = e[4U];
    e[4U] = f4 | mask;
    r = pre;
    r5 = pre + (uint32_t)5U;
    r0 = r[0U];
    r1 = r[1U];
    r2 = r[2U];
    r3 = r[3U];
    r4 = r[4U];
    r51 = r5[1U];
    r52 = r5[2U];
    r53 = r5[3U];
    r54 = r5[4U];
    f10 = e[0U];
    f11 = e[1U];
    f12 = e[2U];
    f13 = e[3U];
    f14 = e[4U];
    a0 = acc[0U];
    a1 = acc[1U];
    a2 = acc[2U];
    a3 = acc[3U];
    a4 = acc[4U];
    a01 = a0 + f10;
    a11 = a1 + f11;
    a21 = a2 + f12;
    a31 = a3 + f13;
    a41 = a4 + f14;
    a02 = r0 * a01;
    a12 = r1 * a01;
    a22 = r2 * a01;
    a32 = r3 * a01;
    a42 = r4 * a01;
    a03 = a02 + r54 * a11;
    a13 = a12 + r0 * a11;
    a23 = a22 + r1 * a11;
    a33 = a32 + r2 * a11;
    a43 = a42 + r3 * a11;
    a04 = a03 + r53 * a21;
    a14 = a13 + r54 * a21;
    a24 = a23 + r0 * a21;
    a34 = a33 + r1 * a21;
    a44 = a43 + r2 * a21;
    a05 = a04 + r52 * a31;
    a15 = a14 + r53 * a31;
    a25 = a24 + r54 * a31;
    a35 = a34 + r0 * a31;
    a45 = a44 + r1 * a31;
    a06 = a05 + r51 * a41;
    a16 = a15 + r52 * a41;
    a26 = a25 + r53 * a41;
    a36 = a35 + r54 * a41;
    a46 = a45 + r0 * a41;
    t0 = a06;
    t1 = a16;
    t2 = a26;
    t3 = a36;
    t4 = a46;
    l0 = t0 + (uint64_t)0U;
    tmp0 = l0 & (uint64_t)0x3ffffffU;
    c01 = l0 >> (uint32_t)26U;
    l1 = t1 + c01;
    tmp1 = l1 & (uint64_t)0x3ffffffU;
    c11 = l1 >> (uint32_t)26U;
    l2 = t2 + c11;
    tmp2 = l2 & (uint64_t)0x3ffffffU;
    c21 = l2 >> (uint32_t)26U;
    l3 = t3 + c21;
    tmp3 = l3 & (uint64_t)0x3ffffffU;
    c31 = l3 >> (uint32_t)26U;
    l4 = t4 + c31;
    tmp4 = l4 & (uint64_t)0x3ffffffU;
    c4 = l4 >> (uint32_t)26U;
    l = tmp0 + c4 * (uint64_t)5U;
    tmp01 = l & (uint64_t)0x3ffffffU;
    c5 = l >> (uint32_t)26U;
    tmp11 = tmp1 + c5;
    o0 = tmp01;
    o1 = tmp11;
    o2 = tmp2;
    o3 = tmp3;
    o4 = tmp4;
    acc[0U] = o0;
    acc[1U] = o1;
    acc[2U] = o2;
    acc[3U] = o3;
    acc[4U] = o4;
    Hacl_Poly1305_32_poly1305_finish(out, k, ctx);
  }
}

void
Hacl_Chacha20Poly1305_32_aead_encrypt(
  uint8_t *k,
  uint8_t *n1,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t mlen,
  uint8_t *m,
  uint8_t *cipher,
  uint8_t *mac
)
{
  Hacl_Chacha20_chacha20_encrypt(mlen, cipher, m, k, n1, (uint32_t)1U);
  {
    uint8_t tmp[64U] = { 0U };
    uint8_t *key;
    Hacl_Chacha20_chacha20_encrypt((uint32_t)64U, tmp, tmp, k, n1, (uint32_t)0U);
    key = tmp;
    Hacl_Chacha20Poly1305_32_poly1305_do_32(key, aadlen, aad, mlen, cipher, mac);
  }
}

uint32_t
Hacl_Chacha20Poly1305_32_aead_decrypt(
  uint8_t *k,
  uint8_t *n1,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t mlen,
  uint8_t *m,
  uint8_t *cipher,
  uint8_t *mac
)
{
  uint8_t computed_mac[16U] = { 0U };
  uint8_t tmp[64U] = { 0U };
  uint8_t *key;
  Hacl_Chacha20_chacha20_encrypt((uint32_t)64U, tmp, tmp, k, n1, (uint32_t)0U);
  key = tmp;
  Hacl_Chacha20Poly1305_32_poly1305_do_32(key, aadlen, aad, mlen, cipher, computed_mac);
  {
    uint8_t res0 = (uint8_t)255U;
    uint8_t z;
    uint32_t res;
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
      {
        uint8_t uu____0 = FStar_UInt8_eq_mask(computed_mac[i], mac[i]);
        res0 = uu____0 & res0;
      }
    }
    z = res0;
    if (z == (uint8_t)255U)
    {
      Hacl_Chacha20_chacha20_encrypt(mlen, m, cipher, k, n1, (uint32_t)1U);
      res = (uint32_t)0U;
    }
    else
    {
      res = (uint32_t)1U;
    }
    return res;
  }
}

