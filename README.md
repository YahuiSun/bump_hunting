# Hunting multiple bumps in graphs

The introduction of these files are as follows. For any enquiry, please feel free to contact Yahui SUN: https://yahuisun.com 


# Datasets

The DBLP dataset is crawled by ourselves from the DBLP website. Two files can be extracted from "DBLP.zip": "DBLP_1094k_keywords.txt" and "DBLP_1094k_collaborations.txt", which contain keywords of researhchers and collaborations between researchers respectively. There are 1,094,552 researhchers and 6,911,318 collaborations in total. This dataset is not small. <b>You can probably find your name or your friends' names inside!</b> 
```diff
- text in red
+ text in green
! text in orange
# text in gray
```
1) DBLP_1094k_keywords.txt: The items in each line are: AuthorName, his or her keywords.
2) DBLP_1094k_collaborations.txt: The items in each line are: Author1, Author2 (this is a collaboration; the way to calculate pairwise Jaccard distances is in our paper).


The Twitter and Flickr datasets were collected by Nikolakaki et al. for the paper: Nikolakaki, Sofia Maria, et al. "Mining tours and paths in activity networks." Proceedings of the 2018 World Wide Web Conference on World Wide Web. International World Wide Web Conferences Steering Committee, 2018. The introduction of our generated file "Austin_graph.stp" from the original Twitter and Flickr datasets is as follows.
1) The items in each line in the vertex section (e.g. V 0 1.000000 0.000000 152567815 30.3960943 -97.7334045) are: V, Vertex_ID, Twitter_prize, Flickr_prize, Label, Location1, Location2 (the labels are from the original Twitter and Flickr datasets, and are like vertex IDs; these locations are real longitudes and latitudes; due to the space limitation, we only use Twitter prizes in our paper).
2) The items in each line in the edge section (e.g. Edge 62 38136 0.048737) are: Edge, Vertex_ID1, Vertex_ID2, edge cost (these edge costs are road distances from the original Twitter and Flickr datasets).

<b>We use codes in the "read_DBLP_data" and "read_Austin_graph" regions in the following "bumphunting.cpp" to load these datasets.</b>



# C++ codes 

The C++ source codes are in <b>bumphunting.cpp</b>. 

There are more than five thousands lines of codes. <b>It is recommended to fold all the regions of codes for easy reading</b> (by pressing Ctrl+M+O in VisualStudio). 

Running these codes requires some header files in the Boost library: https://www.boost.org/ (e.g. #include <boost/graph/adjacency_list.hpp>) and my own YS-Graph-Library: https://github.com/YahuiSun/YS-Graph-Library (e.g. #include <subgraph_unordered_map.h>).

After making the header files ready, all the experiment results in our paper can be produced by runnning the codes in the "experiments" region, i.e., you can run:

int main()
{

   srand(time(NULL)); //  seed random number generator   
   
   auto begin = std::chrono::high_resolution_clock::now();
   
   experiments();
   
   auto end = std::chrono::high_resolution_clock::now();
   
   double runningtime = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() / 1e9; // s
   
   cout << "END    runningtime: " << runningtime << "s" << endl;
   
   getchar();
   

}

<b>There are so many experiments. You may prefer to run them seperately on a cloud.</b>

To read these C++ codes in detail, I suggest to start from the "experiments" region. You may then trace the more detailed codes in other regions like "GBHA" etc. It takes some time to look through all these codes. We give some directions on these codes as follows. Again, for any enquiry, please feel free to contact Yahui SUN: https://yahuisun.com 

1) The codes of our ABHA are below "// ABHA subgraph_unordered_map"
2) The codes of the greedy bump hunting algorithms in our paper are below "// original bump hunting algorithms"
3) The codes of other bump hunting algorithms are below "// our bump hunting algorithms"
4) The codes of counting the number of concrete bumps are below "// statistics; approximating the number of Concrete Bumps"
5) The codes of conducting experiments are below "// Experiments"
6) The codes of comparing greedy bump hunting algorithms with our adaptions are below "// compare original and adapted bump hunting algorithms"
7) The codes of comparing other community detection algorithms with our GBHA are below "// FastNewman2004 and FastVincent2008"
