/* program to time several sorting algorithms on data sets of various sizes
 */

 #include <stdio.h>
 #include <stdlib.h>   // for malloc, free
 #include <time.h>     // for time
 
 /* * * * * * * * * * * quicksort and helper functions * * * * * * * * * * */
 
 /** *******************************************************************************
  * procedure implements the partition operation, following Loop Invariant 1a      *
  *    the Reading on Quicksort referenced above                                   *
  *    in brief: array segment has pivot, then small, unprocessed, large elements  *
  *              both unprocessed endpoints examined, swapping done in line        *
  * @param   a      the array containing the segment to be partitioned             *
  * @param   size   the size of array a                                            *
  * @param   left   the index of the first array element in the partition          *
  * @param   right  the index of the last array element in the partitionn          *
  * @post    a[left] is moved to index mid, with left <= mid <= right              *
  * @post    elements between left and right are permuted, so that                 *
  *             a[left], ..., a[mid-1] <= a[mid]                                   *
  *             a[mid+1], ..., a[right] >= a[mid]                                  *
  * @post    elements outside left, ..., right are not changed                     *
  * @returns  mid                                                                  *
 / *********************************************************************************/
 int basicPartition (int a[ ], int size, int left, int right) {
   int pivot = a[left];
   int l_spot = left+1;
   int r_spot = right;
   int temp;
   
   while (l_spot <= r_spot) {
     while( (l_spot <= r_spot) && (a[r_spot] >= pivot))
       r_spot--;
     while ((l_spot <= r_spot) && (a[l_spot] <= pivot)) 
       l_spot++;
                            // l_spot = 1, r_spot = 0
     // if misplaced small and large values found, swap them
     if (l_spot < r_spot) {
       temp = a[l_spot];
       a[l_spot] = a[r_spot];
       a[r_spot] = temp;
       l_spot++;
       r_spot--;
       }
   }
 
   // swap a[left] with biggest small value
   temp = a[left];
   a[left] = a[r_spot];
   a[r_spot] = temp;
   return r_spot;
 }
 
 /** *******************************************************************************
  * Quicksort helper function                                                      *
  * @param  a  the array to be processed                                           *
  * @param  size  the size of the array                                            *
  * @param  left  the lower index for items to be processed                        *
  * @param  right the upper index for items to be processed                        *
  * @post  sorts elements of a between left and right                              *
  *********************************************************************************/
 void basicQuicksortHelper (int a [ ], int size, int left, int right) {
   if (left > right)
     return;
   int mid = basicPartition (a, size, left, right);
   basicQuicksortHelper (a, size, left, mid-1);
   basicQuicksortHelper (a, size, mid+1, right);
 }
 
 /** *******************************************************************************
  * quicksort, main function                                                       *
  * @param  a  the array to be sorted                                              *
  * @param  n  the size of the array                                               *
  * @post  the first n elements of a are sorted in non-descending order            *
   ********************************************************************************/
 void basicQuicksort (int a [ ], int n) {
   basicQuicksortHelper (a, n, 0, n-1);
 }
 
 /* * * * * * * * improved quicksort and helper functions * * * * * * * * * * */
 
 /** *******************************************************************************
  * procedure implements the partition operation, following Loop Invariant 1a      *
  *    the Reading on Quicksort referenced above                                   *
  *    in brief: array segment has pivot, then small, unprocessed, large elements  *
  *              both unprocessed endpoints examined, swapping done in line        *
  * @param   a      the array containing the segment to be partitioned             *
  * @param   size   the size of array a                                            *
  * @param   left   the index of the first array element in the partition          *
  * @param   right  the index of the last array element in the partitionn          *
  * @post    a[left] is moved to index mid, with left <= mid <= right              *
  * @post    elements between left and right are permuted, so that                 *
  *             a[left], ..., a[mid-1] <= a[mid]                                   *
  *             a[mid+1], ..., a[right] >= a[mid]                                  *
  * @post    elements outside left, ..., right are not changed                     *
  * @returns  mid                                                                  *
 / *********************************************************************************/
 int imprPartition (int a[ ], int size, int left, int right) {
   int temp;
   int randIndex = left + (rand() % (right - left + 1));
   temp = a[randIndex];
   a[randIndex] = a[left];
   a[left] = temp;

   int pivot = a[left];
   int l_spot = left+1;
   int r_spot = right;
   
   while (l_spot <= r_spot) {
     while( (l_spot <= r_spot) && (a[r_spot] >= pivot))
       r_spot--;
     while ((l_spot <= r_spot) && (a[l_spot] <= pivot)) 
       l_spot++;
 
     // if misplaced small and large values found, swap them
     if (l_spot < r_spot) {
       temp = a[l_spot];
       a[l_spot] = a[r_spot];
       a[r_spot] = temp;
       l_spot++;
       r_spot--;
       }
   }
 
   // swap a[left] with biggest small value
   temp = a[left];
   a[left] = a[r_spot];
   a[r_spot] = temp;
   return r_spot;
 }
 
 /** *******************************************************************************
  * Quicksort helper function                                                      *
  * @param  a  the array to be processed                                           *
  * @param  size  the size of the array                                            *
  * @param  left  the lower index for items to be processed                        *
  * @param  right the upper index for items to be processed                        *
  * @post  sorts elements of a between left and right                              *
  *********************************************************************************/
 void imprQuicksortHelper (int a [ ], int size, int left, int right) {
   if (left > right)
     return;
   int mid = imprPartition (a, size, left, right);
   imprQuicksortHelper (a, size, left, mid-1);
   imprQuicksortHelper (a, size, mid+1, right);
 }
 
 /** *******************************************************************************
  * quicksort, main function                                                       *
  * @param  a  the array to be sorted                                              *
  * @param  n  the size of the array                                               *
  * @post  the first n elements of a are sorted in non-descending order            *
   ********************************************************************************/
 void imprQuicksort (int a [ ], int n) {
   imprQuicksortHelper (a, n, 0, n-1);
 }
 
 /* * * * * * * * * * * * procedures to check sorting correctness  * * * * * * * * * */
 
 /** *******************************************************************************
  * check all array elements have values 0, 2, 4, . . ., 2(n-1)                    *
  * @param  a  the array to be sorted                                              *
  * @param  n  the size of the array                                               *
  * returns  "ok" if array contains required elements; "NO" if not                 *
  *********************************************************************************/
 
 char * checkAscValues (int a [ ], int n) {
   for (int i = 0; i < n; i++) {
     if (a[i] != 2*i) {
       printf ("%4d %4d", i, a[i]);
       return "NO";
     }
   }
   return "ok";
 }
 
 /** *******************************************************************************
  * check all array elements are in non-descending order                           *
  * @param  a  the array to be sorted                                              *
  * @param  n  the size of the array                                               *
  * returns  "ok" if array elements in non-descending order; "NO" otherwise        *
  *********************************************************************************/
 
 char * checkAscending (int a [ ], int n) {
   for (int i = 0; i < n-1; i++) {
     if (a[i] > a[i+1])
       return "NO";
   }
   return "ok";
 }
 
 /** *******************************************************************************
  * driver program for testing and timing quicksort algorithms                     *
   ********************************************************************************/
 int main ( ) {
   // print headings
   printf ("                    Data Set                   Times\n");
   printf ("Algorithm             Size     Ascending Order   Random Order  Descending Order\n");
 
   int size;
   for (size = 40000; size <= 5120000; size *= 2) {
       // create control data set arrays
      int * asc = (int *) malloc (size * sizeof(int));   //array with ascending data
      int * ran = (int *) malloc (size * sizeof(int));   //array with random data
      int * des = (int *) malloc (size * sizeof(int));   // array with descending data
      
      int i;
      for (i = 0; i< size; i++) {
         asc[i] = 2*i;
         ran[i] = rand();
         des[i] = 2*(size - i - 1); 
      } 
 
      // timing variables
      clock_t start_time, end_time;
      double elapsed_time;
 
      // copy to test arrays
      int * tempAsc = (int *) malloc (size * sizeof(int));
      int * tempRan = (int *) malloc (size * sizeof(int));
      int * tempDes = (int *) malloc (size * sizeof(int));
 
      /* * * * * * * * * test of basic quicksort * * * * * * * * * * * * * * */
      for (i = 0; i< size; i++) {
         tempAsc[i] = asc[i];
         tempRan[i] = ran[i];
         tempDes[i] = des[i];
      }
      
      // timing for basoc quicksort
      printf ("basic quicksort    %7d", size);
      // ascending data
      start_time = clock ();
      printf("\n%i\n", 1);

      basicQuicksort (tempAsc, size);
      end_time = clock();
      elapsed_time = (end_time - start_time) / (double) CLOCKS_PER_SEC;
      printf ("%13.1lf", elapsed_time);
      printf ("  %2s", checkAscValues (tempAsc, size));
 
      // tandom data
      start_time = clock ();
      printf("\n%i\n", 2);

      basicQuicksort (tempRan, size);
      end_time = clock();
      elapsed_time = (end_time - start_time) / (double) CLOCKS_PER_SEC;
      printf ("%11.1lf", elapsed_time);
      printf ("  %2s", checkAscending (tempRan, size));
 
      // descending data
      start_time = clock ();
      printf("\n%i\n", 3);

      basicQuicksort (tempDes, size);
      
      end_time = clock();
      elapsed_time = (end_time - start_time) / (double) CLOCKS_PER_SEC;
      printf ("%14.1lf", elapsed_time);
      printf ("  %2s", checkAscValues (tempDes, size));
      printf ("\n");
 
 
      /* * * * * * * * * test of improved quicksort * * * * * * * * * * * * * * */
      for (i = 0; i< size; i++) {
         tempAsc[i] = asc[i];
         tempRan[i] = ran[i];
         tempDes[i] = des[i];
      }
      
      // timing for improved quicksort
      printf ("improved quicksort %7d", size);
      
      // ascending data
      start_time = clock ();
      printf("\n%i\n", 4);

      imprQuicksort (tempAsc, size);
      end_time = clock();
      elapsed_time = (end_time - start_time) / (double) CLOCKS_PER_SEC;
      printf ("%13.1lf", elapsed_time);
      printf ("  %2s", checkAscValues (tempAsc, size));
 
      // random data
      start_time = clock ();
      printf("\n%i\n", 5);

      imprQuicksort (tempRan, size);
      end_time = clock();
      elapsed_time = (end_time - start_time) / (double) CLOCKS_PER_SEC;
      printf ("%11.1lf", elapsed_time);
      printf ("  %2s", checkAscending (tempRan, size));
 
      // descending data
      start_time = clock ();
      printf("\n%i\n", 6);

      imprQuicksort (tempDes, size);
      end_time = clock();
      elapsed_time = (end_time - start_time) / (double) CLOCKS_PER_SEC;
      printf ("%14.1lf", elapsed_time);
      printf ("  %2s", checkAscValues (tempDes, size));
      printf ("\n\n");
      
      // clean up copies of test arrays
      free (tempAsc);
      free (tempRan);
      free (tempDes);
 
      // clean up original test arrays
      free (asc);
      free (ran);
      free (des);
      
   } // end of loop for testing procedures with different array sizes
 
   return 0;
 }