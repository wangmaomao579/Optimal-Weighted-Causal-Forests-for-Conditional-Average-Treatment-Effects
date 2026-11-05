library(Metrics)
library(data.table)
library(Rsolnp)
library(MASS)
library(kernlab)
library(expm)
library(pracma)
library(Matching)
library(Matrix)
library(MatchIt)
library(mvtnorm)
library(quadprog)
library(Biobase)
library(mgcv)
library(splines)
library(strucchange)
library(tmvtnorm)
library(grf)
library(randomForest)
library(causalTree)
library(rlearner)
library(bartCause)
library(tidyr)
library(ggplot2)
library(reshape2)
library(xgboost)

n<-500
n_test <- 100
dim_p <- 7

Covariance <- function(corr.struct = "AR", n, p) {
  Work_M <- diag(n)
  if (corr.struct == "CS") {
    for (i in 1:n) {
      for (j in 1:n) {
        if (i != j) Work_M[i, j] = p
      }
    }
  }
  if (corr.struct == "AR") {
    for (i in 1:n) {
      for (j in 1:n) {
        Work_M[i, j] = p^(abs(i - j))
      }
    }
  }
  return(Work_M)
}

mean.f <- function(f) {
  nn <- 1000000
  x <- runif(nn, min = 0, max = 1)
  mean.f <- mean(f(x))
}

# 定义所有的f函数（保持不变）
f_1 <- function(x) { y <- sin(1.5*x); return(y) }
f_2 <- function(x) { y <- x^3 + 1.5*(x-0.5)^2; return(y) }
f_3 <- function(x) { y <- dnorm(x, 0.5, 0.8^2); return(y) }
f_4 <- function(x) { y <- sin(exp(-0.5*x)); return(y) }
f_5 <- function(x) {
  y <- ifelse(x < 0.3, 
              sin(5 * x), 
              ifelse(x < 0.7, 
                     0.5 * x^2 + cos(3 * x),
                     exp(-2 * x) + 0.2 * x))
  return(y)
}
f_6 <- function(x) { y <- 1 / (1 + exp(-3 * x)) + sin(2 * x); return(y) }
f_11 <- function(x) { y <- cos(1.5*x); return(y) }
f_22 <- function(x) { y <- (2*x-1)^2; return(y) }
f_44 <- function(x) { y <- sin(2*pi*x)/(2-sin(2*pi*x)); return(y) }
f_33 <- function(x) { y <- x*cos(2*pi*x); return(y) }
f_55 <- function(x) {
  y <- ifelse(x < 0.3, x^2,
              ifelse(x < 0.7, sin(5 * x),
                     exp(-x) + 0.3 * cos(3 * x)))
  return(y)
}
f_66 <- function(x) { y <- x^3 - 2 * x^2 + sin(pi * x); return(y) }

# 定义h1和h2函数（保持不变）
h1 <- function(X) {
  X <- as.matrix(X)
  if(ncol(X) < 7) {
    stop("X must have at least 6 columns")
  }
  result <- f_1(X[,1]) * f_2(X[,2]) + 
    f_3(X[,3]) * f_4(X[,4]) + 
    f_5(X[,5]) * f_6(X[,6]) +
    sin(f_1(X[,1]) + f_2(X[,2])) * cos(f_3(X[,3]) + f_4(X[,4])) +
    exp(-(f_5(X[,5]) - f_6(X[,6]))^2)
  
  if(ncol(X) > 6) {
    extra_cols <- X[, -c(1:6), drop=FALSE]
    result <- result + rowSums(exp(2 * extra_cols)) }
  return(result)
}
h2 <- function(X) {
  X <- as.matrix(X)
  if(ncol(X) < 7) {
    stop("X must have at least 6 columns") }
  result <- f_11(X[,1]) * f_22(X[,2]) + 
    f_33(X[,3]) * f_44(X[,4]) + 
    f_55(X[,5]) * f_66(X[,6]) +
    exp(-(f_11(X[,1]) - f_22(X[,2]))^2) * 
    sin(f_33(X[,3]) * f_44(X[,4])) +
    sqrt(abs(f_55(X[,5])) + abs(f_66(X[,6])))
  
  if(ncol(X) > 6) {
    extra_cols <- X[, -c(1:6), drop=FALSE]
    result <- result + rowSums(sin(2 * extra_cols))
  }
  
  return(result)
}

matpower <- function(a, alpha) {
  a <- round((a + t(a))/2, 7)
  tmp <- eigen(a)
  return(tmp$vectors %*% diag((tmp$values)^alpha) %*% t(tmp$vectors))
}

discretize <- function(y, h) {
  n <- length(y); m <- floor(n/h)
  y <- y + .00001*mean(y)*rnorm(n)
  yord <- y[order(y)]
  divpt <- numeric()
  for(i in 1:(h-1)) divpt <- c(divpt, yord[i*m+1])
  y1 <- rep(0, n)
  y1[y < divpt[1]] <- 1
  y1[y >= divpt[h-1]] <- h
  for(i in 2:(h-1)) y1[(y >= divpt[i-1]) & (y < divpt[i])] <- i
  return(y1)
}

sir <- function(x, y, h, r, ytype) {
  p <- ncol(x); n <- nrow(x)
  signrt <- matpower(var(x), -1/2)
  xc <- t(t(x) - apply(x, 2, mean))
  xst <- xc %*% signrt
  if(ytype == "continuous") ydis <- discretize(y, h)
  if(ytype == "categorical") ydis <- y
  yless <- ydis; ylabel <- numeric()
  for(i in 1:n) {
    if(var(yless) != 0) {
      ylabel <- c(ylabel, yless[1]); yless <- yless[yless != yless[1]]
    }
  }
  ylabel <- c(ylabel, yless[1])
  prob <- numeric(); exy <- numeric()
  for(i in 1:h) prob <- c(prob, length(ydis[ydis == ylabel[i]])/n)
  for(i in 1:h) exy <- rbind(exy, apply(xst[ydis == ylabel[i], ], 2, mean))
  sirmat <- t(exy) %*% diag(prob) %*% exy
  return(list(sirmat = sirmat, yhat = signrt %*% eigen(sirmat)$vectors[, 1:r]))
}

bic <- function(x, y, h, ytype, criterion, method) {
  maximizer <- function(x, y) return(x[order(y)[length(y)]])
  r <- 2; n <- dim(x)[1]; p <- dim(x)[2]
  if(method == "sir") candmat <- sir(x, y, h, r, ytype)$sirmat
  out <- eigen(candmat); lam <- out$values
  if(criterion == "lal") {
    gn <- numeric()
    for(k in 0:p) {
      if(k == 0) gn <- c(gn, 0) else
        gn <- c(gn, sum(lam[1:k]) - (2*lam[1])*n^(-1/2)*(log(n))^(1/2)*k)
    }
  }
  return(list(rhat = maximizer(0:p, gn), rcurve = gn))
}

sun.index <- function(i, S) {
  sun.index <- 0
  for(j in i:S) sun.index <- sun.index + 1/j
  return(sun.index)
}

# 数据生成
sigma.dataset_csv <- Covariance(corr.struct = "AR", n = dim_p, p = 0.5)
dataset_csv <- rtmvnorm(n, mean = rep(0, dim_p), sigma = sigma.dataset_csv, 
                        lower = rep(0, dim_p), upper = rep(1, dim_p))
dataset <- data.matrix(dataset_csv)
Xdata <- as.matrix(dataset)

e <- 0.5
Tr <- rbinom(n, 1, e) 
true.delta <- h1(dataset) - h2(dataset)

erro1 <- rnorm(n, mean = 0, sd = 2)
erro2 <- rnorm(n, mean = 0, sd = 3)
erro.treat <- erro1
erro.contr <- erro2
ydata <- Tr * h1(dataset) + (1 - Tr) * h2(dataset) + erro1 * Tr + erro2 * (1 - Tr)

treat.x <- Xdata[which(Tr == 1), ]
treat.y <- ydata[Tr == 1]
contr.x <- Xdata[which(Tr == 0), ]
contr.y <- ydata[Tr == 0]
true.delta <- h1(dataset) - h2(dataset)
pair.delta <- numeric(n)
bic0 <- bic(x = contr.x, y = contr.y, h = 5, ytype = "continuous", 
            criterion = "lal", method = "sir")
rx0 <- (Xdata %*% sir(x = contr.x, y = contr.y, h = 5, r = bic0$rhat, 
                      ytype = "continuous")$yhat)
bic1 <- bic(x = treat.x, y = treat.y, h = 5, ytype = "continuous", 
            criterion = "lal", method = "sir")
rx1 <- (Xdata %*% sir(x = treat.x, y = treat.y, h = 5, r = bic0$rhat, 
                      ytype = "continuous")$yhat)
std_X_treat <- rx1[which(Tr == 1), ]
std_X_treat_contr <- rx1[which(Tr == 0), ]
std_X_contr <- rx0[which(Tr == 0), ]
std_X_contr_treat <- rx0[which(Tr == 1), ]
nearest.neighbors.treat <- matchpt(as.matrix(std_X_treat), 
                                   as.matrix(std_X_treat_contr))[, 1]
nearest.neighbors.contr <- matchpt(as.matrix(std_X_contr), 
                                   as.matrix(std_X_contr_treat))[, 1]
treat.pair.data.y <- contr.y[nearest.neighbors.treat]
contr.pair.data.y <- treat.y[nearest.neighbors.contr]
pair.delta[which(Tr == 1)] <- treat.y - treat.pair.data.y
pair.delta[which(Tr == 0)] <- contr.pair.data.y - contr.y
data.train <- data.frame(
  Y = ydata,
  Tr = Tr,
  X1 = dataset[, 1],
  X2 = dataset[, 2],
  X3 = dataset[, 3],
  X4 = dataset[, 4],
  X5 = dataset[, 5],
  X6 = dataset[, 6],
  X7 = dataset[, 7]
)
p <- dim(dataset)[2]
cf <- causalForest(formula = Y ~ X1 + X2 + X3 + X4 + X5 + X6 + 
                     X7, data = data.train, treatment = Tr, split.Rule = "fit", 
                   split.Honest = TRUE, split.Bucket = FALSE, cv.option = "fit", 
                   cv.Honest = TRUE, minsize = 10, mtry = floor(p/2), 
                   nodesize = 3, num.trees = 100, ncov_sample = floor(p/3), 
                   ncolx = p, sample.size.total = n, sample.size.train.frac = 0.9,
                   control = rpart.control(cp = 0.01, maxdepth = 5))

rf_mu1 <- randomForest(x = dataset[Tr == 1, ], y = ydata[Tr == 1], ntree = 100, mtry = floor(p/2), nodesize = 20)
rf_mu0 <- randomForest(x = dataset[Tr == 0, ], y = ydata[Tr == 0], ntree = 100, mtry = floor(p/2), nodesize = 20)
mu1_hat <- predict(rf_mu1,newdata = dataset)
mu0_hat <- predict(rf_mu0,newdata = dataset)
ps_model <- glm(Tr ~ .,data = data.frame(Tr = Tr, dataset),family = binomial(link = "logit"))
e_hat <- predict(ps_model,newdata = data.frame(dataset),type = "response")
# R-Learner
X_train <- as.matrix(dataset)
m_model <- xgboost(
  x = X_train,
  y = ydata,
  objective = "reg:squarederror",
  nrounds = 500
)

m_hat <- predict(
  m_model,
  newdata = X_train
)

Y_resid <- ydata - m_hat
W_resid <- Tr - e_hat
W_resid_safe <- W_resid

W_resid_safe[
  abs(W_resid_safe) < 0.05
] <- ifelse(
  W_resid_safe[
    abs(W_resid_safe) < 0.05
  ] >= 0,
  0.05,
  -0.05
)
tau_pseudo <- Y_resid / W_resid_safe
tau_weight <- W_resid_safe^2
tau_model <- xgboost(
  x = X_train,
  y = tau_pseudo,
  weights = tau_weight,
  objective = "reg:squarederror",
  nrounds = 500
)

RLearner.pred.train <- predict(tau_model, newdata = X_train)
DR_pseudo <- mu1_hat - mu0_hat + Tr * (ydata - mu1_hat) / e_hat - (1 - Tr) * (ydata - mu0_hat) / (1 - e_hat)

rf_DR <- randomForest(x = dataset, y = DR_pseudo, ntree = 100, mtry = floor(p/2), nodesize = 20)

DRLearner.pred.train <- predict(rf_DR, newdata = dataset)

bart_fit <- bartc(
  response = ydata,
  treatment = Tr,
  confounders = Xdata,
  method.rsp = "bart",
  method.trt = "bart",
  p.scoreAsCovariate = TRUE,
  estimand = "ate",
  keepTrees = TRUE,
  keepCall = FALSE,
  verbose = FALSE)
BART.pred.train <- fitted(
  bart_fit,
  type = "icate"
)

BART.pred.train <- as.numeric(
  BART.pred.train
)

treatment_idx <- which(Tr == 1)
control_idx <- which(Tr == 0)
treatment_sample <- cf$inbag[treatment_idx, ]
control_sample <- cf$inbag[control_idx, ]

n_samples <- nrow(cf$data)
n_trees <- length(cf$trees)

treatment_indices <- which(cf$treatment == 1)
control_indices <- which(cf$treatment == 0)
n_treatment_samples <- length(treatment_indices)
n_control_samples <- length(control_indices)

nodeMatrix_treatment <- matrix(0, nrow = n_treatment_samples, ncol = n_trees)
nodeMatrix_control <- matrix(0, nrow = n_control_samples, ncol = n_trees)

for (i in 1:n_trees) {
  tree <- cf$trees[[i]]
  nodeMatrix_treatment[, i] <- tree$where[treatment_indices]
  nodeMatrix_control[, i] <- tree$where[control_indices]
}

rownames(nodeMatrix_treatment) <- treatment_indices
rownames(nodeMatrix_control) <- control_indices

count_in_same_node_treatment <- sapply(1:n_trees, function(j) {
  column_treatment <- nodeMatrix_treatment[, j]
  unique_elements_treatment <- unique(column_treatment)
  
  count_in_same_node_treatment_thisCol <- sapply(unique_elements_treatment, function(x) {
    this_idx_treatment <- which(column_treatment == x)
    if(length(this_idx_treatment) > 0 && !is.null(treatment_sample)) {
      this_count_treatment <- sum(treatment_sample[this_idx_treatment, j], na.rm = TRUE)
    } else {
      this_count_treatment <- length(this_idx_treatment)
    }
    return(this_count_treatment)
  })
  
  sapply(column_treatment, function(x) {
    if(is.na(x)) {
      return(NA)
    }
    idx <- which(x == unique_elements_treatment)
    if(length(idx) > 0) {
      return(count_in_same_node_treatment_thisCol[idx])
    } else {
      return(0)
    }
  })
})

count_in_same_node_control <- sapply(1:n_trees, function(j) {
  column_control <- nodeMatrix_control[, j]
  unique_elements_control <- unique(column_control)
  
  count_in_same_node_control_thisCol <- sapply(unique_elements_control, function(x) {
    this_idx_control <- which(column_control == x)
    if(length(this_idx_control) > 0 && !is.null(control_sample)) {
      this_count_control <- sum(control_sample[this_idx_control, j], na.rm = TRUE)
    } else {
      this_count_control <- length(this_idx_control)
    }
    return(this_count_control)
  })
  
  sapply(column_control, function(x) {
    if(is.na(x)) {
      return(NA)
    }
    idx <- which(x == unique_elements_control)
    if(length(idx) > 0) {
      return(count_in_same_node_control_thisCol[idx])
    } else {
      return(0)
    }
  })
})

P_treatment <- treatment_sample / count_in_same_node_treatment
P_control <- control_sample / count_in_same_node_control

pred.hat.datla <- predict(cf, newdata = data.train, predict.all = TRUE)$individual
delta.hat.mat <- pred.hat.datla

effect_errors <- matrix(NA, nrow = nrow(pred.hat.datla), ncol = ncol(pred.hat.datla))
for(i in 1:ncol(pred.hat.datla)) {
  effect_errors[, i] <- pair.delta - pred.hat.datla[, i]
}

ydata_treatment_samples <- ydata[treatment_idx]
ydata_control_samples <- ydata[control_idx]
P_treatment[is.na(P_treatment)] <- 0
P_control[is.na(P_control)] <- 0
ydata_treatment_samples_mat <- matrix(rep(ydata_treatment_samples, n_trees), ncol = n_trees)
ydata_control_samples_mat <- matrix(rep(ydata_control_samples, n_trees), ncol = n_trees)
erro.hat.treatment <- ydata_treatment_samples_mat - rowMeans(P_treatment * ydata_treatment_samples)
erro.hat.control <- ydata_control_samples_mat - P_control * ydata_control_samples

a1 <- t(effect_errors[, 1:n_trees]) %*% effect_errors[, 1:n_trees] + diag(0.000001, n_trees)
weighted_squared_treatment <- colSums(2 * erro.hat.treatment^2 * P_treatment)
weighted_squared_control <- colSums(2 * erro.hat.control^2 * P_control)
weighted_squared_error <- weighted_squared_treatment + weighted_squared_control 
a2 <- matrix(-weighted_squared_error, n_trees, 1)
a3 <- t(rbind(matrix(1, nrow = 1, ncol = n_trees), diag(n_trees), -diag(n_trees)))
a4 <- rbind(1, matrix(0, nrow = n_trees, ncol = 1), matrix(-1, nrow = n_trees, ncol = 1))
QP <- solve.QP(a1, a2, a3, a4, 1)
optimal_w <- QP$solution
optimal_w <- as.matrix(optimal_w)
optimal_w <- optimal_w * (optimal_w > 0)
optimal_w <- optimal_w / sum(optimal_w)

tPE <- numeric(n_trees)
weightwRF <- numeric(n_trees)
weightCRF <- numeric(n_trees)

for(index_s in 1:n_trees) {
  sample.num <- sample(n, n, replace = TRUE)
  tau.hat <- delta.hat.mat[, index_s]
  
  errorOOB <- 0
  OOB <- 0
  for(i in 1:n) {
    if(sum(sample.num == i) == 0) {
      errorOOB <- errorOOB + abs(pair.delta[i] - tau.hat[i])
      OOB <- OOB + 1
    }
  }
  
  if(OOB > 0) {
    tPE[index_s] <- (errorOOB/OOB)
    weightwRF[index_s] <- (OOB/errorOOB)^2
  } else {
    tPE[index_s] <- Inf
    weightwRF[index_s] <- 0
  }
}

weightwRF <- weightwRF / sum(weightwRF)

order_tPE <- order(tPE)
for(index_s in 1:n_trees) {
  weightCRF[index_s] <- sun.index(which(order_tPE == index_s), n_trees)
}
weightCRF <- weightCRF / sum(weightCRF)

equal.weight <- rep(1/n_trees, n_trees)
sigma.test <- Covariance(corr.struct = "AR", n = dim_p, p = 0.5)

X_test <- rtmvnorm(
  n_test,
  mean = rep(0, dim_p),
  sigma = sigma.test,
  lower = rep(0, dim_p),
  upper = rep(1, dim_p)
)
X_test <- as.matrix(X_test)
Tr_test <- rbinom(n_test, 1, e)
erro1_test <- rnorm(
  n_test,
  mean = 0,
  sd = 2
)

erro2_test <- rnorm(
  n_test,
  mean = 0,
  sd = 3
)

Y_test <- Tr_test * h1(X_test) +
  (1 - Tr_test) * h2(X_test) +
  erro1_test * Tr_test +
  erro2_test * (1 - Tr_test)

true.delta.test <- h1(X_test) - h2(X_test)

data.test <- data.frame(
  Y = Y_test,
  Tr = Tr_test,
  X1 = X_test[, 1],
  X2 = X_test[, 2],
  X3 = X_test[, 3],
  X4 = X_test[, 4],
  X5 = X_test[, 5],
  X6 = X_test[, 6],
  X7 = X_test[, 7]
)
pred.test.all <- predict(cf, newdata = data.test, predict.all = TRUE)$individual

BART.pred <- predict(
  bart_fit,
  newdata = X_test,
  type = "icate"
)

BART.pred <- as.numeric(
  BART.pred
)
RLearner.pred <- predict(
  tau_model,
  newdata = as.matrix(X_test)
)


# DR-Learner
DRLearner.pred <- predict(
  rf_DR,
  newdata = X_test
)


WCRF.pred <- pred.test.all %*% optimal_w
CRF.pred <- pred.test.all %*% equal.weight
WRF.pred <- pred.test.all %*% weightwRF
QRF.pred <- pred.test.all %*% weightCRF


error.list <- list(
  WCRF = true.delta.test - WCRF.pred,
  CRF = true.delta.test - CRF.pred,
  WRF = true.delta.test - WRF.pred,
  QRF = true.delta.test - QRF.pred,
  R_Learner = true.delta.test - RLearner.pred,
  DR_Learner = true.delta.test - DRLearner.pred,
  BART = true.delta.test - BART.pred   
)


method_names <- c(
  "WCRF",
  "CRF",
  "WRF",
  "QRF",
  "R_Learner",
  "DR_Learner",
  "BART"
)

method_labels <- c(
  "WCRF",
  "CRF",
  "WRF",
  "Cesàro RF",
  "R",
  "DR",
  "BART"
)


final_summary_table <- data.frame(
  
  n = n,
  
  Method = method_labels,
  
  MSE = sapply(
    method_names,
    function(m) {
      mean(error.list[[m]]^2, na.rm = TRUE)
    }
  ),
  
  MAE = sapply(
    method_names,
    function(m) {
      mean(abs(error.list[[m]]), na.rm = TRUE)
    }
  )
  
)

final_summary_table$Method <- factor(
  final_summary_table$Method,
  levels = method_labels
)

final_summary_table <- final_summary_table[
  order(final_summary_table$Method),
]

final_summary_table$MSE <- round(
  final_summary_table$MSE,
  7
)

final_summary_table$MAE <- round(
  final_summary_table$MAE,
  7
)

rownames(final_summary_table) <- NULL

print(final_summary_table)


final_plot_data <- final_summary_table
