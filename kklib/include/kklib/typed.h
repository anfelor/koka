#pragma once
#ifndef KK_TYPED_H
#define KK_TYPED_H
/*---------------------------------------------------------------------------
  Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Support definitions for the typed backend (src/Backend/Typed/CGen.hs).

#define kt_pun(T,x) ({ __typeof__(x) _kt_x = (x); T _kt_y; _Static_assert(sizeof(T)==sizeof(_kt_x),"kt_pun"); memcpy(&_kt_y,&_kt_x,sizeof(T)); _kt_y; })
#define kt_box_integer(i)  kt_pun(kk_box_t,i)
#define kt_unbox_integer(b) kt_pun(kk_integer_t,b)
#define kt_box_string(s)   kt_pun(kk_box_t,s)
#define kt_unbox_string(b) kt_pun(kk_string_t,b)
#define kt_box_datatype(d) kk_datatype_box(d)
#define kt_unbox_datatype(b) kk_datatype_unbox(b)
#define kt_unreachable() kk_fatal_error(EFAULT,"typed backend: unreachable")
static inline kk_block_t* kt_box_as_ptr(kk_box_t b, kk_context_t* ctx) {
  return kk_datatype_as_ptr(kk_datatype_unbox(b),ctx);
}
static inline kk_box_t kt_box_from_block(kk_block_t* b, kk_context_t* ctx) {
  return kk_datatype_box(kk_datatype_from_ptr(b,ctx));
}
static inline kk_tag_t kt_tag(kk_box_t b, kk_context_t* ctx) {
  return kk_datatype_tag(kk_datatype_unbox(b),ctx);
}
static inline kk_tag_t kt_heap_tag(kk_box_t b, kk_context_t* ctx) {
  return kk_block_tag(kt_box_as_ptr(b,ctx));
}
#define kt_yielded(T) ({ T _kt_y = {0}; kk_valuetype_unbox_from_any((kk_box_t*)&_kt_y,sizeof(T),kk_box_any(_ctx),KK_OWNED,_ctx); _kt_y; })
static inline __attribute__((always_inline)) kk_box_t kt_box_dup_inline(kk_box_t b, kk_context_t* ctx) {
  return kk_box_dup(b,ctx);
}
static inline __attribute__((always_inline)) kk_box_t kt_datatype_dup_inline(kk_box_t b, kk_context_t* ctx) {
  return kk_datatype_box(kk_datatype_dup(kk_datatype_unbox(b),ctx));
}
static inline __attribute__((always_inline)) kk_box_t kt_datatype_ptr_dup_inline(kk_box_t b, kk_context_t* ctx) {
  return kk_datatype_box(kk_datatype_ptr_dup(kk_datatype_unbox(b),ctx));
}
// plug the hole of a unique context (`kk_cctx_apply_linear`); an empty context has no hole
static inline kk_box_t kt_ctx_plug(kk_box_t res, kk_box_t hole, kk_box_t child, kk_context_t* _ctx) {
  if kk_likely(!kk_box_eq(hole,kk_box_null())) {
    kk_assert_internal(kk_block_is_unique(kk_ptr_unbox(res,_ctx)));
    *kk_internal_ptr_unbox(hole,_ctx) = child;
    return res;
  }
  return child;
}
// append a unique context to a unique one: plug its `res` into the hole and keep its hole
static inline void kt_ctx_append(kk_box_t* res, kk_box_t* hole, kk_box_t res2, kk_box_t hole2, kk_context_t* _ctx) {
  if (!kk_box_eq(hole2,kk_box_null())) { *res = kt_ctx_plug(*res,*hole,res2,_ctx); *hole = hole2; }
}
// copy the path of a shared context (`kk_cctx_copy`), which consumes the shared `res`
static inline void kt_ctx_copy(kk_box_t* res, kk_box_t* hole, kk_context_t* _ctx) {
  if (!kk_box_eq(*hole,kk_box_null()) && !kk_block_is_unique(kk_ptr_unbox(*res,_ctx))) {
    kk_box_t* h = NULL;
    *res = kk_cctx_copy(*res,kk_internal_ptr_unbox(*hole,_ctx),&h,_ctx);
    *hole = kk_internal_ptr_box(h,_ctx);
  }
}
// plug the hole of a context that may be shared (`kk_cctx_apply`): copy its path if it is
static inline kk_box_t kt_ctx_copy_plug(kk_box_t res, kk_box_t hole, kk_box_t child, kk_context_t* _ctx) {
  if kk_unlikely(kk_box_eq(hole,kk_box_null())) return child;
  if kk_likely(kk_block_is_unique(kk_ptr_unbox(res,_ctx))) {
    *kk_internal_ptr_unbox(hole,_ctx) = child;
    return res;
  }
  return kk_cctx_copy_apply(res,kk_internal_ptr_unbox(hole,_ctx),child,_ctx);
}
static inline kk_block_t* kt_block_clear(kk_block_t* b, kk_ssize_t scan_fsize, kk_tag_t tag, kk_context_t* _ctx) {
  b->header.scan_fsize = (uint8_t)scan_fsize; b->header.tag = tag;
  // hide that the result is `b`: otherwise clang infers that a `lazy-C` function returns its
  // cell, and `lazy-eval-locked` returns the cell itself instead of tail calling `lazy-C`
  #if defined(__GNUC__) || defined(__clang__)
  __asm__("" : "+r"(b));
  #endif
  return b;
}
// credits come from box blocks, which are always allocated with `kk_malloc_small`
static inline void kt_reuse_drop(kk_reuse_t r, kk_context_t* _ctx) {
  if (r != kk_reuse_null) { kk_assert_internal(kk_block_is_unique(r)); kk_free_small(r,_ctx); }
}
static inline void kt_reuse_free(kk_reuse_t r, kk_context_t* _ctx) {
  kk_assert_internal(r != kk_reuse_null && kk_block_is_unique(r)); kk_free_small(r,_ctx);
}
static inline bool kt_open_is(kk_box_t b, kk_string_t tag, kk_context_t* _ctx) {
  struct kt_open_s { kk_block_t _block; kk_string_t _tag; };
  return kk_string_ptr_eq_borrow(((struct kt_open_s*)kt_box_as_ptr(b,_ctx))->_tag, tag);
}

#endif // include guard
