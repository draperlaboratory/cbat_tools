#include <stdio.h>
#include <stdlib.h>

int calculate_price(int num_orders) {

    int price_1 = 25; // Price per item for 1000 or more orders
    int price_2 = 50; // Price per item for 100 to 1000 orders
    int price_3 = 100; // Price per item for less than 100 orders

    if ((num_orders > 0) && (num_orders % 100 == 0)) {
        if (num_orders < 1000) {
            return price_2 * num_orders;
        } else {
            return price_1 * num_orders;
	}
    }

    if ((num_orders <= 100) && (num_orders % 10 == 0)) {
        if (num_orders < 20) {
            return -2;
	} else {
	    return price_3 * num_orders;
	}
    }

    return -1;

}

int main(int arcc, char *argv[]) {

    const char *user_input = argv[1];
    int num_orders = (int) strtol(user_input, NULL, 0);

    int price = calculate_price(num_orders);

    if (price == -1) {
        printf("Small orders must be in multiples of tens, large orders in multpiples of hundreds\n");
	return 1;
    } else if (price == -2) {
        printf("Minimum order is 20\n");
	return 1;
    } else {
        printf("Total price: %d.00\n", price);
	return 0;
    }

}
