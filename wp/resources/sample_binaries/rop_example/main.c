int test1(int a, int b)
{
	return a + b;
}

int main()
{
    int i = 0;
    int ret = 0;

    for (i=0; i<10; i++)
    {
        ret += test1(i, i++);
    }

    return ret;
}
