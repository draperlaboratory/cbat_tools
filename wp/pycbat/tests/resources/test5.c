typedef struct mystruct
{
    int f1;
    char f2;
} mystruct;

int foo(mystruct *x, char y)
{
    int bar;
    bar = x->f1;
    return 3 + bar;
}
