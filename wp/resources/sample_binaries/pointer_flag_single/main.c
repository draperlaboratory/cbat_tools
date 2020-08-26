int foo(int * x){
    int y = 3;
    *x = 0xdeadbeef;
    return y;
}

int main(int argc, char* argv[])
{
    return 0;
}
