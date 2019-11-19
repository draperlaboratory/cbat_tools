#include "csmith.h"


static long __undefined;


struct S0 {
    uint32_t  f0;
};

#pragma pack(push)
#pragma pack(1)
struct S1 {
    unsigned f0 : 30;
    volatile unsigned f1 : 10;
    uint8_t  f2;
};
#pragma pack(pop)


static struct S0 g_2 = {4294967295UL};
static struct S0 * volatile g_3 = &g_2;
static struct S1 g_4 = {7887,24,0x57L};



static struct S1  func_1(void);




static struct S1  func_1(void)
{ 
    (*g_3) = (g_2 , g_2);
    return g_4;
}





int main (int argc, char* argv[])
{
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2.f0, "g_2.f0", print_hash_value);
    transparent_crc(g_4.f0, "g_4.f0", print_hash_value);
    transparent_crc(g_4.f1, "g_4.f1", print_hash_value);
    transparent_crc(g_4.f2, "g_4.f2", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}

