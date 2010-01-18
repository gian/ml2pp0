#include <stdio.h>
#include <stdlib.h>

/*@ declare ccc i32 @print_int ( i32 ) */
int print_int( int i )
{
	printf("%d\n", i);
}

/*@ declare ccc i32 @input_int ( i32 ) */
int input_int ( int x )
{
	int i = 0;
	printf("Please enter a number: ");
	scanf("%d", &i);
	return i;
}

/*@ declare ccc i32 @print ( i8* ) */
int print ( char *s )
{
	printf("%s\n",s);
	return 0;
}
