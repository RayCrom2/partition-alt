/* program to time several partition algorithms on data sets of various sizes
 */

/** ***************************************************************************
 * @remark  program to time several partition algorithms on data sets         *
 * of various sizes                                                           *
 *                                                                            *
 * @author Henry M. Walker                                                    *
 * @file  partition-alt.c                                                     *
 * @date  August 7, 2022, revised November 30, 2024                           *
 *                                                                            *
 * @remark References                                                         *
 * @remark Henry M. Walker, Pascal: Problem Solving and Structured Program    *
 *         Design, Little, Brown, and Company, 1987, pages 500-506            *
 * @remark Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivset, and      *
 *         Clifford Stein, Introduction to Algorithms, Third Edition          *
 *         The MIT Press, 2009, pages170-185                                  *
 * @remark Reading on Quicksort, https://blue.cs.sonoma.edu/~hwalker/courses  *
 *                 /415-sonoma.fa22/readings/reading-quicksort.php            *
 *                                                                            *
 * @remark People participating with Problem/Progra Discussions:              *
 *         None                                                               *
 *                                                                            *
 *****************************************************************************/

 #include <stdio.h>
 #include <stdlib.h>   // for malloc, free
 #include <time.h>     // for time
 
 #define printCopyTime 0  // 1 =  print times to copy arrays; 0 = omit this output
 
 /** *******************************************************************************
  * structure to identify both the name of a partition algorithm and               *
  * a pointer to the function that performs the partition                          *
  * the main function utilizes this struct to define an array of partition         *
  * algorithms, based on different loop invariants, in to be timed by this program.*
  *********************************************************************************/
 typedef struct algs {
   char * name;
 int (*proc) (int [ ], int, int, int);
 } partitionType;
 
 /** *******************************************************************************
  * procedure to help check partition worked correctly                             *
  * @param  pivotSpot   index where pivot was supposed to be moved                 *
  * @param correctPivot value that should have been used as the pivot in partition *
  * @param a            the array being partitioned                                *
  * @param first        the index at the start of the segment to be partitioned    *
  * @param last         the index at the end of the segment to be partitioned      *
  * @post returns NO1 if correctPivot is not at index pivotSpot                    *
  *               NO2 if at least one elements betreew index first and pivotSpot   *
  *                      are greater than correctPivot                             * 
  *               NO3 if at least one elements betreew index pivotSpot and last    *
  *                      are less than correctPivot                                *
  *               OK! if the array segment passes the above checks                 * 
  *********************************************************************************/
 char * checkPivotSpot (int pivotSpot, int correctPivot, int a [ ], int first, int last) {
  // printf("\na[pivotSpot]: %d\n", a[pivotSpot]);

   if( a[pivotSpot] != correctPivot) {
     return "NO1";
   }
   int i;
   for (i = first; i < pivotSpot; i++) {
     if (a[i] > a[pivotSpot])
       return "NO2";
   }
   for (i = pivotSpot+1; i <= last; i++) {
     if (a[i] < a[pivotSpot])
       return "NO3";
   }
  //  printf("\npicotSpot: %d\n", pivotSpot);
  // printf("a[pivotSpot]: %d\n", a[pivotSpot]);
  // printf("Correct picot: %d\n", correctPivot);
   return "OK!";
 }
 
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
 int invariant1a (int a[ ], int size, int left, int right) {
   int pivot = a[left];
   int l_spot = left+1;
   int r_spot = right;
   int temp;
   
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
  * procedure implements the partition operation, following Loop Invariant 1b      *
  *    the Reading on Quicksort referenced above                                   *
  *    in brief: array segment has pivot, then small, large, unprocessed elements  *
  *              left unprocessed endpoints examined, swapping uses swap function  *
  * @param   a      the array containing the segment to be partitioned             *
  * @param   size   the size of array a                                            *
  * @param   left   the index of the first array element in the partition          *
  * @param   right  the index of the last array element in the partitionn          *
  * @post    a[left] is moved to index mid, with left <= mid <= right              *
  * @post    elements between left and right are permuted, so that                 *
  *             a[left], ..., a[mid-1] <= a[mid]                                   *
  *             a[mid+1], ..., a[right] >= a[mid]                                  *
  * @post    elements outside left, ..., right are not changed                     *
  * @returns mid                                                                   *
  *********************************************************************************/
 
 /* invariant 1b:  partition, swapping many interations, plus separate swap */
 int invariant1b (int a[ ], int size ,int first, int last) {
   int pivot = a[first];
   int left;
   int right = last;
   int temp;
   
   for (left = first+1; left <= right;) {
     if (a[left] < pivot) {
       left++;
     }
     else {
       temp = a[left];
       a[left] = a[right];
       a[right] = temp;
       right--;
     }
   }
 
   temp = a[right];
   a[right] = a[first];
   a[first] = temp;
 
   return right;
 }

 /** *******************************************************************************
  * procedure implements the partition operation, following Loop Invariant 5      *
  *    the Reading on Quicksort referenced above                                   *
  *    in brief: array segment has pivot, then small, large, unprocessed elements  *
  *              left unprocessed endpoints examined, swapping uses swap function  *
  * @param   a      the array containing the segment to be partitioned             *
  * @param   size   the size of array a                                            *
  * @param   left   the index of the first array element in the partition          *
  * @param   right  the index of the last array element in the partitionn          *
  * @post    a[left] is moved to index mid, with left <= mid <= right              *
  * @post    elements between left and right are permuted, so that                 *
  *             a[left], ..., a[mid-1] <= a[mid]                                   *
  *             a[mid+1], ..., a[right] >= a[mid]                                  *
  * @post    elements outside left, ..., right are not changed                     *
  * @returns mid                                                                   *
  *********************************************************************************/
 
 /* invariant 5:  partition, swapping many interations, plus separate swap */
 int invariant5 (int a[ ], int size ,int first, int last) {
  int pivot = a[last];
  int left;
  int right = last - 1;
  int temp;
  
  for (left = first; left <= right;) {
    if (a[left] < pivot) {
      left++;
    }
    else {
      temp = a[left];
      a[left] = a[right];
      a[right] = temp;
      right--;
    }
  }

  temp = a[left];
  a[left] = a[last];
  a[last] = temp;

  return left;
}
 
/** *******************************************************************************
  * procedure implements the partition operation, following Loop Invariant 7      *
  *    the Reading on Quicksort referenced above                                   *
  *    in brief: array segment has pivot, then small, large, unprocessed elements  *
  *              left unprocessed endpoints examined, swapping uses swap function  *
  * @param   a      the array containing the segment to be partitioned             *
  * @param   size   the size of array a                                            *
  * @param   left   the index of the first array element in the partition          *
  * @param   right  the index of the last array element in the partitionn          *
  * @post    a[left] is moved to index mid, with left <= mid <= right              *
  * @post    elements between left and right are permuted, so that                 *
  *             a[left], ..., a[mid-1] <= a[mid]                                   *
  *             a[mid+1], ..., a[right] >= a[mid]                                  *
  * @post    elements outside left, ..., right are not changed                     *
  * @returns mid                                                                   *
  *********************************************************************************/
 
 /* invariant 7:  partition, swapping many interations, plus separate swap */
 int invariant7 (int a[ ], int size ,int first, int last) {
  int pivot = a[last];
  int left;
  int right = last - 1;
  int temp;
  
  for (left = last - 1; left >= first;) {
    if (a[left] < pivot) {
      left--;
    }
    else {
      temp = a[left];
      a[left] = a[right];
      a[right] = temp;
      left--;
      right--;
    }
  }

  temp = a[right + 1];
  a[right + 1] = a[last];
  a[last] = temp;

  return right + 1;
}

/** *******************************************************************************
  * procedure implements the kth element operation,      *
  *    in brief: array segment is partitioned until it finds the kth smallest element at the pivot  *
  * @param   a      the array containing the segment to be searched             *
  * @param   size   the size of array a                                            *
  * @param   k      the kth smallest element                                             *
  * 
  * @post    elements in array permuted, so that                 *
  *             a[left], ..., a[(size/2)-1] <= a[size/2]                                   *
  *             a[(size/2)+1], ..., a[right] >= a[size/2]                                  *
  * @returns value of kth smallest element                                         *
  *********************************************************************************/
 
 /* kth element */
int kthElement (int a[], const int size, const int k){
  if (k > size)
    return -1;
  return kthElementHelper(a, size, k, 0, size - 1, -1);
}

/** *******************************************************************************
  * procedure implements the kth element operation,      *
  *    in brief: array segment is partitioned until it finds the kth smallest element at the pivot  *
  * @param   a      the array containing the segment to be searched             *
  * @param   size   the size of array a                                            *
  * @param   k      the kth smallest element                                             *
  * @param   l_index      the first element in the array to be searched                             *
  * @param   r_index      the last element in the array to be searched                               *
  * @param   middle      the location of the pivot to compare                                       *
  
  * @post    elements in array permuted, so that                 *
  *             a[left], ..., a[(size/2)-1] <= a[size/2]                                   *
  *             a[(size/2)+1], ..., a[right] >= a[size/2]                                  *
  * @returns value of kth smallest element                                         *
  *********************************************************************************/
 
 /* kth element helper */
int kthElementHelper (int a[], const int size, const int k, int l_index, int r_index, int middle){
  middle = invariant5(a, size, l_index, r_index);
  if (middle == k - 1)
    return a[k - 1];
  if (middle < k - 1)
    return kthElementHelper(a, size, k, middle + 1, r_index, middle);
  return kthElementHelper(a, size, k, l_index, middle - 1, middle);
}

 /** *******************************************************************************
  * driver program for testing and timing partition algorithms                     *
  *********************************************************************************/
 
 int main ( ) {
   // identify partition procedures used and their decriptive names
   #define numAlgs  4
   partitionType procArray [numAlgs] = {{"invariant 1a ", invariant1a   },
                                        {"invariant 1b ", invariant1b   },
                                        {"invariant 5  ", invariant5 },
                                        {"invariant 7  ", invariant7 }};
 
   // print output headers
   printf ("timing/testing of partition functions\n");
   // print headings
   printf ("               Data Set                             Times\n");
   printf ("Algorithm        Size     Ascending Order       Random Order  Descending Order\n");
 
   int size;
   int reps;
   int maxreps = 1000;
 
   // organize data sets of increasing size for ascending, random, and descending data
   for (size = 100000; size <= 1600000; size *= 2) {
       // create control and initial data set arrays
      int * asc = (int *) malloc (size * sizeof(int));   //array with ascending dpaata
      int * ran = (int *) malloc (size * sizeof(int));   //array with random data
      int * des = (int *) malloc (size * sizeof(int));   // array with descending data
      
      int i;
      for (i = 0; i< size; i++) {
         asc[i] = 2*i;
         ran[i] = rand();
         des[i] = 2*(size - i - 1); 
      }
      
      // copy to test arrays
      int * tempAsc = malloc (size * sizeof(int));
      int * tempRan = malloc (size * sizeof(int));
      int * tempDes = malloc (size * sizeof(int));
 
      // repeat for each algorithm
      for (int alg = 0; alg < numAlgs; alg++) {
 
        // identify function and data set size
        printf ("%s %7d", procArray[alg].name, size);
         // timing variables
        clock_t start_time, end_time;
        double copy_time, elapsed_time;
        int pivotSpot;
 
        /* * * * * * * * * * * * * * * * * * * * * * * *
         *      test and time algorithm:  algProc[alg] *
         * * * * * * * * * * * * * * * * * * * * * * * */
 
        /* * * * * * * test ascending data * * * * * * */
 
        // determine average time to copy array
        start_time = clock ();
        for (reps = 0; reps < maxreps; reps++) {
          for (i = 0; i< size; i++) {
            tempAsc[i] = asc[i];
          }
        }

        end_time = clock();
        copy_time = ((end_time - start_time) / (double) CLOCKS_PER_SEC );

        if (printCopyTime)
          printf ("copy time:  %10.1lf\n", copy_time);
      
        // timing for algorithm
       start_time = clock ();
       for (reps = 0; reps < maxreps; reps++) {
         for (i = 0; i< size; i++) {
           tempAsc[i] = asc[i];
         }
           pivotSpot = procArray[alg].proc (tempAsc, size, 0, size-1);
       }
        end_time = clock();
        elapsed_time = (end_time - start_time) / (double) CLOCKS_PER_SEC;
        printf ("%13.1lf ", elapsed_time - copy_time);

        if (alg >= 2){
          printf ("%3s  ", checkPivotSpot (pivotSpot, (size - 1)* 2, tempAsc, 0, size-1));
        }
        else{
          printf ("%3s  ", checkPivotSpot (pivotSpot, 0, tempAsc, 0, size-1));
        }
        /* * * * * * * test random data * * * * * * */
 
        // determine time to copy array
        start_time = clock ();
        for (reps = 0; reps < maxreps; reps++) {
          for (i = 0; i< size; i++) {
            tempRan[i] = ran[i];
          }
        }

        
        end_time = clock();
        copy_time = ((end_time - start_time) / (double) CLOCKS_PER_SEC );
        if (printCopyTime)
          printf ("copy time:  %10.1lf", copy_time);
        
        // timing for algorithm
        start_time = clock ();
        for (reps = 0; reps < maxreps; reps++) {
          for (i = 0; i< size; i++) {
            tempRan[i] = ran[i];
          }
          pivotSpot = procArray[alg].proc (tempRan, size, 0, size-1);
          }
        end_time = clock();
        elapsed_time = (end_time - start_time) / (double) CLOCKS_PER_SEC;
        printf ("%13.1lf ", elapsed_time - copy_time);
        if (alg >= 2){
          printf ("%3s ", checkPivotSpot (pivotSpot, ran[size - 1], tempRan, 0, size-1));
        }
        else{
          printf ("%3s ", checkPivotSpot (pivotSpot, ran[0], tempRan, 0, size-1));
        }
      
        /* * * * * * * test descending data * * * * * * */
 
        // determine time to copy array
        start_time = clock ();
        for (reps = 0; reps < maxreps; reps++) {
          for (i = 0; i< size; i++) {
            tempDes[i] = des[i];
          }
        }
        end_time = clock();
        copy_time = ((end_time - start_time) / (double) CLOCKS_PER_SEC );

        

        if (printCopyTime)
          printf ("copy time:  %10.1lf", copy_time);
      
        // timing for algoirthm
        start_time = clock ();
        for (reps = 0; reps < maxreps; reps++) {
          for (i = 0; i< size; i++) {
            tempDes[i] = des[i];
          }
          pivotSpot = procArray[alg].proc (tempDes, size, 0, size-1);
        }

        end_time = clock();
        elapsed_time = (end_time - start_time) / (double) CLOCKS_PER_SEC;
        printf ("%13.1lf ", elapsed_time - copy_time);
        if (alg >= 2){
          printf ("%3s ", checkPivotSpot (pivotSpot, 0, tempDes, 0, size-1));
        }
        else{
          printf ("%3s ", checkPivotSpot (pivotSpot, 2*(size - 1), tempDes, 0, size-1));
        }
        printf("\n");
        for (int i = 0, k = 1; i < size / 50000; i++, k++){
          if (kthElement(tempAsc, size, k) != i*2 && kthElement(tempDes, size, k) != 2*(size - i - 1)){
            printf("\nFAIL!\n");
          }
        }
        printf("\nPassed\n");


        
 
      } // end of loop for testing an algorithm
 
      // leave blank line before output of next size
      printf ("\n");
 
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