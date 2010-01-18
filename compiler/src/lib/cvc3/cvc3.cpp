#include <stdlib.h>

#define CVCEXPR int

typedef struct {
	int x;
	float y;
	char z;
} foo_t;

extern "C" CVCEXPR *cvc_plusExpr (CVCEXPR *lhs, CVCEXPR *rhs)
{
	foo_t *f = (foo_t *)malloc(sizeof(foo_t));

	f->x = 42;
	f->y = 123.4;
	f->z = 'z';

	return (CVCEXPR *)f;
}

extern "C" CVCEXPR *cvc_nullExpr ( void )
{
	return (CVCEXPR*) NULL;
}

