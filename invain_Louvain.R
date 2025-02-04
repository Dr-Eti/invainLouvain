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
  comm_list_fun <- c(unlist(unique(nodes_comm_list_fun$community)))
  n_comm_fun <- length(comm_list_fun) 
  L_fun <- sum(adj_fun)/2                                                               # this is already available outside the function
  #L_fun <- L
  for (comm_j_sum in comm_list_fun) {
    iter_comm_idx <- which(nodes_comm_list_fun$community == comm_j_sum)
    within_comm <- sum(adj_fun[iter_comm_idx,iter_comm_idx])
    degree_comm <- sum(adj_fun[iter_comm_idx,]) 
    modul_iter <- modul_iter + (((within_comm/2)/L_fun) - (degree_comm/(2*L_fun))^2)     # Barabasi, Network Science, eqn. 9.12 p. 340
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


invain_louvain <- function(edges_df, resolution_param = 1, max_iter = 20){
  iter <- 1
  iter_end <- FALSE
  list_adj_mat <- list()
  list_comm_iter <- list()                                                              # nodes communities allocation at each pass
  list_modulmetric_iter <- list()                                                       # modularity of the node-comm allocation at each pass
  set.seed(100879)                                                                      
  adj_output <- nodelist_to_adjmatrix(edges_df)                                         # call own function
  adj_mat_export <- adj_output$adj_mat
  
  ## initialise progress bar
  pb = utils::txtProgressBar(min = 0, max = max_iter, initial = 0, style = 3) 
  
  #### Iterative "passes" (each pass consists of 2 steps)                               #####
  while (!iter_end & iter < max_iter){
    ## stuff needed all the time
    adj_g <- adj_output$adj_mat
    list_adj_mat[[iter]] <- adj_g
    tot_arcs_weigth <- sum(adj_g)
    L <- tot_arcs_weigth/2                                                             # assume undirected
    node_neighbours_list <- apply(adj_g, 1, function(x){
      which(x != 0)
    })
    node_degrees <- apply(adj_g, 1, function(x){
      sum(x)
    })
    node_list <- adj_output$node_list                                                  # alphab. sorted node list
    n_nodes <- adj_output$n_nodes
    n_comm <- n_nodes                                                                  # AT FIRST each node is a community
    comm_list <- paste0(sprintf("cn_%03d", 1:n_nodes),"_",iter)
    nodes_comm_list <- as.data.frame(cbind(node_list, comm_list))                      # Node-communities "dynamic" allocation table
    colnames(nodes_comm_list) <- c("node_name", "community")
    modularity_initial_score <- modularity_score(nodes_comm_list,adj_g)                # Initial modularity score. Calls another function
    
    #### current pass, step 1 - must be looped                                                        ####
    firstpass_repeat <- TRUE
    firstpass_repeat_count <- 1
    max_firstpass_count <- max_iter
    mod_improve_previous <- 0
    while (firstpass_repeat & firstpass_repeat_count < max_firstpass_count){
      ## this is the core of step 1: try change nodes-communities allocation                                          
      starting_allocation <- nodes_comm_list$community                                                    # if the iteration doesn't change the starting community allocation, break out
      rand_node_sort <- sample(n_nodes)                                                                   # EACH time the PASS is iterated visit nodes in random order
      # nodes_comm_list[rand_node_sort, ]
      for(node_i in rand_node_sort){
        guest_own_comm <-  nodes_comm_list$community[node_i]                                              # "guest" is our current node/community, to be merged with different "host" communities
        degree_guest <- as.numeric(node_degrees[node_i])                                                  # guest's degrees
        node_neighbours <- node_neighbours_list[[node_i]]
        if (length(node_neighbours) > 0){                                                                 # if there are neighbouring communities
          node_neighbours_idx <- as.numeric(node_neighbours)                                          
          node_neighbours_comm <- unique(nodes_comm_list$community[node_neighbours_idx])                  # lookup neighbouringcommunities as candidates for a possible merge
          ## [PLEASE CHECK] chose whether or not to detach from current community and then bring back
          nodes_comm_list[node_i,"community"] <- "vacant"                                                 # "detach" node from own community
          #node_neighbours_comm <- node_neighbours_comm[which(node_neighbours_comm != guest_own_comm)]    # briefly entertained the idea of skipping the current community - not sure if this messes up the whole process
          if(length(node_neighbours_comm) > 0){
            mod_gain <- sapply(node_neighbours_comm, function(comm_j){
              host_idx <- which(nodes_comm_list[,"community"] ==  comm_j)  
              if (length(host_idx) > 0){                                                                     
                degree_host_within <- sum(adj_g[host_idx, host_idx])
                degree_host <- sum(adj_g[host_idx,])                                                      # assuming undirected, in-degree = out-degree
                node_to_host <- sum(adj_g[node_i, host_idx]) 
                ## modularity change equation
                (node_to_host/L) - resolution_param*((degree_host*degree_guest)/(2*L^2))                  # see e.g. Barabasi eqn 9.43 and also p. 370. change in modularity due to the move 
              } else {
                0
              }
            })
            test_improve_mod <- max(as.numeric(mod_gain)) > 1e-06
          } else {
            test_improve_mod <- F
          }
          if (test_improve_mod){  
            new_comm <- names(which.max(mod_gain))
          } else {
            new_comm <- guest_own_comm                                                                    # re-attach to current community
          }
          nodes_comm_list$community[node_i] <- new_comm                                                   # update best candidate as new host community   
        }
      }
      ## did this iteration of step 1 achieve an improvement over previous?
      mod_improve_iter <- (modularity_score(nodes_comm_list, adj_g) - mod_improve_previous > 1e-06)
      if (!mod_improve_iter | identical(nodes_comm_list$community, starting_allocation)){
        firstpass_repeat <- FALSE                                                                        # repeating the first pass didn't change the community to which nodes are allocated: break out
      } else {
        firstpass_repeat_count <- firstpass_repeat_count + 1  
      }
    }
    ## Store outputs of step 1 at this PASS iteration
    list_modulmetric_iter[[iter]] <- modularity_score(nodes_comm_list, adj_g)                           # Record modularity at this iteration
    list_comm_iter[[iter]] <- nodes_comm_list                                                           # Record allocation at this iteration
    ## check if any progress has been made since previous pass
    if(iter > 1){
      prev_iter <- iter - 1
      if(list_modulmetric_iter[[iter]] - list_modulmetric_iter[[prev_iter]] < 1e-06){
        iter_end <- TRUE
        optimal_modul <- list_modulmetric_iter[[iter]]
      }
    }
    
    #### current pass, Step 2: collapse nodes into communities                                        ####
    comm_list <- unique(nodes_comm_list[,"community"])                                                # communities from first pass become nodes in the second pass
    n_comm <- length(comm_list)
    agg_nodes_idx <- expand.grid(1:n_comm, 1:n_comm)
    agg_nodes_idx <- agg_nodes_idx[,c(2:1)]
    agg_nodes_idx <- agg_nodes_idx[which(agg_nodes_idx[,2] >= agg_nodes_idx[,1]),]                    # assuming undirected network. This time include self-loop
    colnames(agg_nodes_idx) <- c("source_node","target_node")
    rownames(agg_nodes_idx) <- NULL
    new_arclist_weight <- apply(agg_nodes_idx, 1, function(x){
      a <- as.numeric(x[1])
      b <- as.numeric(x[2])
      nodes_a <- which(nodes_comm_list$community %in% comm_list[a])
      nodes_b <- which(nodes_comm_list$community %in% comm_list[b])
      sum(adj_g[nodes_a, nodes_b])
    })
    from_to_compress <- sapply(agg_nodes_idx, function(x){
      comm_list[x]
    })
    edges_compress_df <- data.frame(source_node = as.character(from_to_compress[,1]),
                                    target_node = as.character(from_to_compress[,2]),
                                    weight = as.numeric(new_arclist_weight),
                                    stringsAsFactors = F)
    adj_compress_output <- nodelist_to_adjmatrix(edges_compress_df)                                    # get compressed adjacency matrix where communities are now nodes
    ## prepare for next iteration
    adj_output <- adj_compress_output
    if(!iter_end){
      iter <- iter + 1
      
      ## update progress bar
      utils::setTxtProgressBar(pb,iter)
    }
  } # end iteration between passes 
  
  ## close progress bar
  close(pb)
  
  ## Backtrack
  for(j in iter:1){                                                               # start from last record
    x <- list_comm_iter[[j]]
    community_iter <- as.matrix(x[2])
    nodes_iter <- as.matrix(x[1])
    if(j < iter){
      community_re_number <- backward_key$community[match(community_iter, backward_key$node_name )]
      backward_key <- as.data.frame(cbind(nodes_iter,  community_re_number))
      colnames(backward_key) <- c("node_name", "community_final")
    } else {
      community_re_number <- match(community_iter, unique(community_iter))
      backward_key <- as.data.frame(cbind(nodes_iter,  community_re_number))
      colnames(backward_key) <- c("node_name", "community_final")
    }
  }
  ## output list
  output_list <- list(louvain_communities = backward_key,
                      modularity = optimal_modul,
                      adj_mat = adj_mat_export)
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

