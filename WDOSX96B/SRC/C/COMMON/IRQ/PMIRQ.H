/*
** PMIRQ.H - functions exported from PMIRQ.WDL
*/

#if !defined(__PMIRQ_H)
#define __PMIRQ_H

void (*__stdcall GetIRQHandler(int))(); 
void __stdcall SetIRQHandler(int, void());

#endif /* __PMIRQ_H */

