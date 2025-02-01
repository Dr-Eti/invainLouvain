## Louvain graph partitioning from scratch in R
##
## Ettore Settanni
## E.Settanni@eng.cam.ac.uk
##
## 08/2020 (Revised: 02/2025)
##
## Version notes: 
## For academic references used see section 00 (info) below





## clear
rm(list = ls())
gc()


## PLEASE: make sure you set a working directory, first
## ----2) in RStudio just click Session--> Set Working Directory --> ...
## --- 1) ...or specify manually e.g. setwd("C:/Users/....")

#### [INFO] Selected resources cited                                                                   ####
# 1) Vincent D Blondel et al (2008) J. Stat. Mech.  - common to Gephi and igraph
# 2) Barabasi A-L, Network Science, https://networksciencebook.com/chapter/9#modularity
# 3) in practice: https://www.r-bloggers.com/community-detection-with-louvain-and-infomap/

## For some blurb of how this malarkey came about:
# https://igraph.discourse.group/t/details-for-cluster-louvain-local-moving-heuristic-for-r-users/380/6

## For an alternative implementations in R (without C-Layer)
## https://rdrr.io/github/AlexChristensen/NetworkToolbox/src/R/louvain.R

#### [INFO] sources of example data                                                                    ####
## Example 1: https://www.r-bloggers.com/community-detection-with-louvain-and-infomap/
## Example 2: https://networksciencebook.com/chapter/9#advanced-9c 
## Example 3: https://medium.com/walmartlabs/demystifying-louvains-algorithm-and-its-implementation-in-gpu-9a07cdd3b010




####                                                                                                   ####
#### 00.0 declare functions                                                                            ####

modularity_score <- function(nodes_comm_list_fun, adj_fun){
  modul_iter <- 0
  comm_list_fun <- unique(nodes_comm_list_fun["community"])
  n_comm_fun <- nrow(comm_list_fun) 
  L_fun <- sum(adj_fun)/2
  
  for (comm_j_sum in 1:n_comm_fun) {
    iter_comm_idx <- as.numeric(nodes_comm_list_fun[which(nodes_comm_list_fun[,"community"]==comm_list_fun[comm_j_sum,"community"]),"node idx in adj"])          # a bit redundant but just in case the adjacency lines are scrambled
    within_comm <- sum(adj_fun[iter_comm_idx,iter_comm_idx])
    degree_comm <- sum(adj_fun[iter_comm_idx,]) 
    modul_iter <- modul_iter + (((within_comm/2)/L_fun) - (degree_comm/(2*L_fun))^2)                                                                              # Barabasi, Network Science, eqn. 9.12 p. 340
  }
  return(modul_iter)
}


nodelist_to_adjmatrix <- function(edges_df){
  ## force undirected
  undirected <- T
  ignore_directed = T                                                     # for now force undirected, later consider moving to argument
  nodes_list <- unique(c(edges_df$source_node,  edges_df$target_node))
  nodes_list <- nodes_list[order(nodes_list, decreasing = FALSE)]        # optional: sort nodes 
  n_nodes <- length(nodes_list)
  mymat <- matrix(0L, nrow = n_nodes, ncol = n_nodes)
  colnames(mymat) <- nodes_list
  rownames(mymat) <- nodes_list
  directed_arc_count <- 0
  for(i in 1:nrow(edges_df)){
    a <- as.character(edges_df$source_node[i])
    b <- as.character(edges_df$target_node[i])
    w <- as.numeric(edges_df$weight[i])
    mymat[a, b] <- w
    ## is it directed
    idx_opposite <- which(edges_df$target_node %in% edges_df$source_node[i])
    if(length(edges_df$source_node[idx_opposite]) !=0){
      if(length(which(edges_df$source_node[idx_opposite] %in% b) >0)){ 
        idx_symmetric <- which(edges_df$source_node[idx_opposite] %in% b)
        idx_keep <- idx_opposite[idx_symmetric]
        if(length(idx_keep)>1){
          warning("duplicate records in arc list detected")
          mytest <- edges_df$weight[idx_symmetric] !=  rep(w, length(idx_keep))
        } else {
          mytest <- edges_df$weight[idx_symmetric] !=  w
        }
        if(length(which(mytest)) > 0){
          ## definitely not symmetric
          undirected <- F
          directed_arc_count <- directed_arc_count + 1
        } else {
          ## unnecessary repetition in the arc list
          warning("redundant records in the arc list detected")
        }
      }
    }
    if(undirected | ignore_directed){
      mymat[b, a] <- w
    } 
  }
  if(!undirected & ignore_directed){
    warning(paste0(directed_arc_count, " directed arcs were detected but ignored"))
  }
  ## output
  out_list <- list(adj_mat = mymat, 
                   node_list = nodes_list,
                   n_nodes = n_nodes)
  return(out_list)
}


invain_louvain <- function(edges_df){
  #### A) obtain adjacency matrix                                                                      #####
  adj_output <- nodelist_to_adjmatrix(edges_df)                                      # call own function
  adj_g <- adj_output$adj_mat
  tot_arcs_weigth <- sum(adj_g)
  L <- tot_arcs_weigth/2                                                             # assume undirected
  
  #### B) Initial nodes-communities allocation #####
  node_list <- adj_output$node_list                                                  # alphab. sorted node list
  n_nodes <- adj_output$n_nodes
  node_list_idx <- match(node_list, node_list)                                       # map node order onto the node adj matrix line names
  #node_list <- (rownames(adj_g))                                                    # equivalent alternative
  #n_nodes <- nrow(adj_g)
  n_comm <- n_nodes                                                                  # AT FIRST each node is a community
  comm_list <- sprintf("cn_%03d", 1:n_nodes)
  nodes_comm_list <- as.data.frame(cbind(node_list_idx, node_list, comm_list))       # Node-communities "dynamic" allocation table
  colnames(nodes_comm_list) <- c("node idx in adj","node_name", "community")
  modularity_initial_score <- modularity_score(nodes_comm_list,adj_g)                # Initial modularity score. compare with Q in Network Toolbox or Brain Connectivity Toolbox
  
  #### C) Iterative "passess"s #####
  ## initialise iterations between passes
  iter_end <- FALSE
  iter <- 1
  max_iter <- 100
  ## initialise lists at each PASS (within random iteration)
  list_comm_iter <- list()                                                                            # pass output 1: node-comm allocation at each pass
  list_modulmetric_iter <- list()                                                                     # pass output 2: modularity of the node-comm allocation at each pass
  ## start EVERYTHING afresh 
  adj_dummy <- adj_g                                                                                  # make a copy of the adjacency matrix 
  n_nodes_dummy <- n_nodes
  node_list_dummy <- node_list
  nodes_comm_list_dummy <- nodes_comm_list
  nodes_comm_list_PASS <- nodes_comm_list
  comm_list_dummy <- comm_list
  n_comm_dummy <- n_comm
  while (isFALSE(iter_end) & iter < max_iter){
    # this serves as stopping criteria
    delta_q <- matrix(0L, n_nodes_dummy, n_comm_dummy)
    rownames(delta_q) <- nodes_comm_list_dummy[,"node idx in adj"]                                      # NODES LABELLING DOESN'T MATTER - THAT'S WHAT THE PACKAGE DOES
    colnames(delta_q) <- nodes_comm_list_dummy[,"community"]
    ## the first pass itself must be repeated in a loop
    flag <- TRUE
    flag_count <- 1
    max_flag_count <- 100
    while (flag & flag_count < max_flag_count){
      ## EACH time the PASS is iterated visit nodes in random order
      #set.seed(100879)                                                                                 # remove this if you want to vary the random sequence every time
      rand_node_sort <- sample(n_nodes_dummy)
      nodes_visit_label_lookup <- nodes_comm_list_dummy[rand_node_sort,]                                # establish correspondence between nodes idx and label after random sorting
      allocation_flag <- nodes_comm_list_dummy[,"community"]                                            # to compare later for stopping
      
    ## C.1)  Classic "FIRST PASS"                                                                     ####
      for (node_i in rand_node_sort) {                                                                  # visit nodes in random sequence
        own_comm <- nodes_comm_list_dummy[node_i,"community"]                                           # initial community will be restored if no modularity gain
        guest_name <- nodes_comm_list_dummy[node_i,"node_name"]
        degree_guest <- sum(adj_dummy[node_i,])                                                         # node's degrees
        ## find & describe node's neighbours
        node_neighbours <- which(adj_dummy[node_i,] > 0)
        if (length(node_neighbours) > 0){
          node_neighbours_names <- names(node_neighbours)
          node_neighbours_idx <- as.numeric(node_neighbours)
          node_neighbours_comm <- nodes_comm_list_dummy[node_neighbours_idx,"community"]
        }
        ## remove node from own community
        nodes_comm_list_dummy[node_i,"community"] <- "vacant"                                                         # TEST: DEACTIVATE TO FULLY MATCH Network toolbox/BCT  PACKAGE RESULTS because they ADD the delta modularity of bringing back the node to its own SINGLETON community
        ## To do: perhaps also check if own community is DISCONNECTED after guest is removed from it (main intuition of Leiden algorithm vs Louvain)
        ## begin local move
        max_gain <- 0
        best_host_community <- "none"
        for (comm_j in 1:n_comm_dummy) {                                                                              # INTENTIONAL to read all communities (initially = nodes) to fill 'delta_q'. As nodes get reassigned some communities may be empty
          host_idx <- which(nodes_comm_list_dummy[,"community"] == comm_list_dummy[comm_j])                           # returns the index (not the name) of filtered nodes associated with a given community at a given stage of the algorithm         
          if (length(host_idx) > 0){                                                                     
            degree_host <- sum(adj_dummy[host_idx,])                                                                  # for undirected, in-degree = out-degree
            if(length(adj_dummy[node_i,host_idx]) > 1) {                                                              # does the potential host community have more than one member?
              node_to_host <- sum(adj_dummy[node_i,host_idx])                                                         # if so, sum weighed arcs connecting potential guest and host (the matrix is symmetric)
            } else {
              node_to_host <- adj_dummy[node_i,host_idx]
            }
            ## Compute modularity gain from local move
            mod_gain_textbk <- (node_to_host/L) - ((degree_host*degree_guest)/(2*L^2))                                # Textbook formula e.g. Barabasi eqn 9.43 and also p. 370 on the algebra deriving modularity gains from general modularity formula. Louvain is a special case
            mod_gain <- (node_to_host) - ((degree_host*degree_guest)/(2*L))                                           # variation foudn in Brain Connectivity Toolbox (BCT) in Matlab, and Network Toolbox in R
            ## also slight difference between Barabasi eqn 9.43 and https://www.r-bloggers.com/community-detection-with-louvain-and-infomap/
            ## record modularity gain
            delta_q[node_i,comm_list_dummy[comm_j]] <- mod_gain                                                        
            ## update best candidate as new host community     
            if (mod_gain > max_gain){                                                                                 # except the neighbours' communities, other communities surely generate negative modularity gain
              best_host_community <- comm_list_dummy[comm_j]
              max_gain <- mod_gain
            } ## endif compare mod gains
          } ## endif there are member nodes in a given community
        } ## stop looping through alternative host communities
        ## pick new host community OR restore previous
        if (max_gain > 0){                                                                  # determines whether or not the FIRT PASS will be iterated again
          nodes_comm_list_dummy[node_i,"community"] <- best_host_community
        } else {
          nodes_comm_list_dummy[node_i,"community"] <- own_comm                             # restore original
          best_host_community <- own_comm                                                   # only for info during debugging
        }
      } ## stop looping through nodes
      ## check stopping creteria for first pass
      if (identical(nodes_comm_list_dummy[,"community"], allocation_flag)){
        flag <- FALSE 
      } 
      flag_count <- flag_count + 1
    } ## end while flag (stop looping first pass)
    ## check if iterations are over
    check_max <- apply(delta_q, 1, max)                                                     # in the presence of ties, there may be multiple max
    new_host <- apply(delta_q, 1, which.max)                                                # index of max, by row (without looping)
    new_host <- new_host[which(check_max > 0)]                                                                               
    if (length(new_host) == 0){
      iter_end <- TRUE
    } 
   
    ## C.2) SECOND PASS ####
    comm_list_dummy <- unique(nodes_comm_list_dummy[,"community"])                                                     # list of unique communities obtained from first pass to become nodes in the second pass
    n_comm_dummy <- length(comm_list_dummy)
    ## initialise new collapsed adjacency matrix for SECOND PASS
    new_adj <- matrix(0L,n_comm_dummy, n_comm_dummy)
    ## Compress network whilst computing modularity over communities for the latest partitioning
    modul_iter <- 0
    for (comm_j_sum in 1:n_comm_dummy) {
      iter_comm_idx <- which(nodes_comm_list_dummy[,"community"]==comm_list_dummy[comm_j_sum])        
      within_comm <- sum(adj_dummy[iter_comm_idx,iter_comm_idx])
      degree_comm <- sum(adj_dummy[iter_comm_idx,]) 
      modul_iter <- modul_iter + (((within_comm/2)/L) - (degree_comm/(2*L))^2)                                          # Barabasi, Network Science, eqn. 9.12 p. 340
      ## COLLAPSE NODES WITHIN SAME CATEGORY
      for (comm_i_sum in 1:n_comm_dummy){
        if(comm_i_sum != comm_j_sum){
          iter_comm_idx_target <- which(nodes_comm_list_dummy[,"community"]==comm_list_dummy[comm_i_sum]) 
          new_adj[comm_j_sum,comm_i_sum] <- sum(adj_dummy[iter_comm_idx,iter_comm_idx_target])
        } else {
          new_adj[comm_j_sum,comm_i_sum] <- within_comm
        }
      }
    }
    ## Link compressed matrix results to original nodes
    if (iter > 1){
      lookup_previous_comms <- unique(nodes_comm_list_PASS[,"community"])                                         # allocation before this pass was performed
      previous_comms <- nodes_comm_list_PASS[,"community"]
      for (i_dummy in 1:n_nodes_dummy){
        lookup_comm <- lookup_previous_comms[i_dummy]                                                             # to avoid filtering after updating contents
        lookup_node_idx <- which(previous_comms == lookup_comm)                                                   # to avoid filtering after updating contents
        nodes_comm_list_PASS[lookup_node_idx,"community"] <- nodes_comm_list_dummy[i_dummy, "community"]
      } 
    } else {
      nodes_comm_list_PASS <- nodes_comm_list_dummy
    }
    ## Store outputs at this iteration
    list_modulmetric_iter[[iter]] <- modularity_score(nodes_comm_list_dummy, adj_dummy)                          # Record modularity at this iteration
    #all.equal(modul_iter, modularity_score(nodes_comm_list_dummy, adj_dummy))                                   # test that the modularity across community is the same
    list_comm_iter[[iter]] <- nodes_comm_list_PASS                                                               # Record allocation at this iteration
    ## re-initialise using compressed adjacency matrix (previous communities become nodes)
    adj_dummy <- new_adj
    n_nodes_dummy <- nrow(adj_dummy)
    node_list_dummy <- sprintf(paste0("n_iter", iter, "_%03d"), 1:n_comm_dummy)
    rownames(adj_dummy) <- node_list_dummy
    colnames(adj_dummy) <- node_list_dummy
    node_list_idx <- match(node_list_dummy, rownames(adj_dummy))
    nodes_comm_list_dummy <- as.data.frame(cbind(node_list_idx,node_list_dummy, comm_list_dummy))
    colnames(nodes_comm_list_dummy) <- c("node idx in adj","node_name", "community")
    ## move on to repeat
    iter <- iter + 1
  } # end iteration between passes 
  
  ## E) prepare output ####
  ## renumber communities
  community_re_number <- match(nodes_comm_list_PASS$community, unique(nodes_comm_list_PASS$community))
  my_own_louvain_communities <- as.data.frame(cbind(nodes_comm_list_PASS$node_name, community_re_number))
  colnames(my_own_louvain_communities) <- c("node_ID", "community_ID")
  
  ## modularity
  my_own_modularity <- as.numeric(list_modulmetric_iter[[iter - 1]])
  
  ## output list
  output_list <- list(louvain_communities = my_own_louvain_communities,
                      modularity = my_own_modularity,
                      adj_mat = adj_g)
  return(output_list)
}


####                                                                                                   ####
#### 01.1 set paths                                                                                    ####
mypath   <- "./CSVs_IN"                                                                                ## if we are accessing a small example for debug
Out_path <- paste0("./CSVs_OUT")                                                                       ## save output generated by the script in a separate folder


#### 01.2 load data (edge list) from csv file                                                          ####
## Assume structure: source_node | target_node | weight
## choose one example
#edges_df  <- read.csv(paste0(mypath, "/edges_df_example01.csv", collapse = " "), header = TRUE)
#edges_df  <- read.csv(paste0(mypath, "/edges_df_example02.csv", collapse = " "), header = TRUE)
edges_df  <- read.csv(paste0(mypath, "/edges_df_example03.csv", collapse = " "), header = TRUE)



#### 01.3 ...or manually enter data (edge list)                                                        #####

## Example 1
## Source: https://www.r-bloggers.com/community-detection-with-louvain-and-infomap/
# edges_df <- data.frame(source_node=character(),
#                          target_node=character(),
#                          weight=numeric(),
#                          stringsAsFactors=FALSE)
# edges_df[1,] <- c("A", "B", 5)
# edges_df[2,] <- c("A", "C", 4)
# edges_df[3,] <- c("A", "E", 1)
# edges_df[4,] <- c("B", "C", 2)
# edges_df[5,] <- c("C", "D", 7)
# edges_df[6,] <- c("D", "F", 3)
# edges_df[7,] <- c("E", "F", 8)




## dummy data 2: https://networksciencebook.com/chapter/9#advanced-9c
# edges_df <- data.frame(source_node=character(),
#                       target_node=character(),
#                       weight=numeric(),
#                       stringsAsFactors=FALSE)# 
# edges_df[1,] <- c("n00", "n02", 1)
# edges_df[2,] <- c("n00", "n03", 1)
# edges_df[3,] <- c("n00", "n05", 1)
# edges_df[4,] <- c("n00", "n04", 1)
# edges_df[5,] <- c("n01", "n02", 1)
# edges_df[6,] <- c("n01", "n04", 1)
# edges_df[7,] <- c("n01", "n07", 1)
# edges_df[8,] <- c("n02", "n06", 1)
# edges_df[9,] <- c("n02", "n05", 1)
# edges_df[10,] <- c("n02", "n04", 1)
# edges_df[11,] <- c("n03", "n07", 1)
# edges_df[12,] <- c("n04", "n10", 1)
# edges_df[13,] <- c("n05", "n11", 1)
# edges_df[14,] <- c("n06", "n11", 1)
# edges_df[15,] <- c("n07", "n06", 1)
# edges_df[16,] <- c("n07", "n05", 1)
# edges_df[17,] <- c("n08", "n15", 1)
# edges_df[18,] <- c("n08", "n11", 1)
# edges_df[19,] <- c("n08", "n09", 1)
# edges_df[20,] <- c("n08", "n10", 1)
# edges_df[21,] <- c("n08", "n14", 1)
# edges_df[22,] <- c("n09", "n14", 1)
# edges_df[23,] <- c("n09", "n12", 1)
# edges_df[24,] <- c("n10", "n14", 1)
# edges_df[25,] <- c("n10", "n11", 1)
# edges_df[26,] <- c("n10", "n12", 1)
# edges_df[27,] <- c("n10", "n13", 1)
# edges_df[28,] <- c("n11", "n13", 1)



# Dummy data #3 from https://medium.com/walmartlabs/demystifying-louvains-algorithm-and-its-implementation-in-gpu-9a07cdd3b010
# edges_df <- data.frame(source_node=character(),
#                        target_node=character(),
#                        weight=numeric(),
#                        stringsAsFactors=FALSE)
# edges_df[1,] <- c("n01", "n02", 1)
# edges_df[2,] <- c("n01", "n03", 1)
# edges_df[3,] <- c("n01", "n04", 1)
# edges_df[4,] <- c("n02", "n01", 1)
# edges_df[5,] <- c("n02", "n03", 1)
# edges_df[6,] <- c("n03", "n01", 1)
# edges_df[7,] <- c("n03", "n02", 1)
# edges_df[8,] <- c("n04", "n01", 1)
# edges_df[9,] <- c("n04", "n05", 1)
# edges_df[10,] <- c("n05", "n04", 1)
# edges_df[11,] <- c("n05", "n06", 1)
# edges_df[12,] <- c("n05", "n07", 1)
# edges_df[13,] <- c("n06", "n05", 1)
# edges_df[14,] <- c("n07", "n05", 1)
# edges_df[15,] <- c("n07", "n08", 1)
# edges_df[16,] <- c("n08", "n07", 1)
# edges_df[17,] <- c("n08", "n09", 1)
# edges_df[18,] <- c("n09", "n08", 1)



####                                                                                                   #####
#### 02.0 Call own louvain function                                                                    #####
own_louvain <- invain_louvain(edges_df)

## print results
#own_louvain$louvain_communities
#own_louvain$modularity

####                                                                                                   ####
#### 03.0 [Optional] Benchmark with igraph                                                             ####
library(igraph)
igraph_g <- graph_from_edgelist(as.matrix(edges_df[,1:2]), directed = FALSE)
E(igraph_g)$weight <- edges_df$weight
adj_g_igraph <- as.matrix(as_adjacency_matrix(igraph_g, attr="weight"))
adj_g_igraph <- adj_g_igraph[order(rownames(adj_g_igraph), decreasing = F), order(rownames(adj_g_igraph), decreasing = F)]
louvain_igraph <- cluster_louvain(igraph_g, 
                             weights = E(igraph_g)$weight)
benchmark_igraph_clust <- cbind(V(igraph_g)$name, louvain_igraph$membership )
benchmark_igraph_clust <- as.data.frame(benchmark_igraph_clust[order(benchmark_igraph_clust[,1], decreasing = F),])
if(length(louvain_igraph$modularity)>1){
  igraph_modularity <- max(louvain_igraph$modularity)
} else {
  igraph_modularity <- louvain_igraph$modularity
}


## compare 
all.equal(adj_g_igraph, own_louvain$adj_mat)                                            # check adjacency matrix is the same
all.equal(unname(benchmark_igraph_clust), unname(own_louvain$louvain_communities))      # check clusters
all.equal(own_louvain$modularity, igraph_modularity)                            # check modularity



#### 03.1 [Optional] Benchmark with Network Toolbox                                                    ####
## becnhmark 2: Network Toolbox / based on Brain Connectivity Toolbox (matlab). 
## resources: 
## -- https://rdrr.io/github/AlexChristensen/NetworkToolbox/src/R/louvain.R
## -- Original: https://sites.google.com/site/bctnet/measures/list
library(NetworkToolbox)                                   
A <- adj_g_igraph 
gamma <- 1                                                                               # resolution parameter, nor relevant in this benchmark
M0 <- 1:ncol(A)   
benchmark_BCT <- louvain(A, gamma, M0)
benchmark_BCT_clust <- cbind(colnames(A), benchmark_BCT$community)
benchmark_BCT_modularity <- benchmark_BCT$Q

all.equal(as.numeric(benchmark_BCT$community), as.numeric(own_louvain$louvain_communities$community_ID))
all.equal(benchmark_BCT$Q, own_louvain$modularity)

#### 03.2 [Optional] Juxtapose results in table                                                        ####
homemade_ext <- cbind(own_louvain$louvain_communities, benchmark_igraph_clust, benchmark_BCT_clust)
colnames(homemade_ext) <- c(colnames(own_louvain$louvain_communities), "IGRAPH_node_label", "IGRAPH_community","BCT_node_label","BCT_community")

modularity_ext <- c(own_louvain$modularity, igraph_modularity, benchmark_BCT_modularity)
names(modularity_ext) <- c("homemade","IGRAPH","BCT")

## print
homemade_ext
modularity_ext

####                                                                                                   ####
#### 04.0 Export to csv                                                                                ####
write.csv(own_louvain$louvain_communities, paste0(Out_path,"/community_myownlouvain.csv"), row.names = FALSE)

