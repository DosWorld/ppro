/**************************************************************************
*
* $Header: E:/RCS/wdosx/0.95/src/wpack/WPACK.H 1.1 1999/06/20 15:43:14 MikeT Exp $
*
***************************************************************************
*
* $Log: WPACK.H $
* Revision 1.1  1999/06/20 15:43:14  MikeT
* Initial check in.
*
*
***************************************************************************/

/**************************************************************************
 * WDOSX-Pack                  Copyright (c) 1999 by Joergen Ibsen / Jibz *
 *                                                    All Rights Reserved *
 *                                                                        *
 * For data and executable compression software:    http://apack.cjb.net/ *
 *                                                  jibz@hotmail.com      *
 **************************************************************************/

#ifndef __WDOSXPACK_H
#define __WDOSXPACK_H

#ifdef __cplusplus
extern "C" {
#endif

/* function prototype */
unsigned int WdosxPack(unsigned char *source,
                       unsigned char *destination,
                       unsigned int length
                      );

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif
