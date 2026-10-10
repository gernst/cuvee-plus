#include <assert.h>

typedef struct {
    int batt_voltages[10]; //Maximum voltage value in battery
    int max_voltage;
} BATTERY_PACK;

extern int __VERIFIER_nondet_int();
extern BATTERY_PACK nondet_BATTERY_PACK();
BATTERY_PACK bpack;

void calc_pack_max() {
  bpack.max_voltage = bpack.batt_voltages[0];
  
  int i = 0;
  while(i < 10) {
    if (bpack.batt_voltages[i] > bpack.max_voltage) {
      bpack.max_voltage = bpack.batt_voltages[i];
    }
    i++;
  }
}
void main() {
  bpack = nondet_BATTERY_PACK();

  calc_pack_max();
  
  int max = bpack.batt_voltages[0];
  for (int i = 0; i < 10; i++) {
      if (bpack.batt_voltages[i] > max) {
          max = bpack.batt_voltages[i];
      }
  }
  assert(max  == bpack.max_voltage);
}
