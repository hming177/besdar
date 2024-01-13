library(MASS)
library(matrixStats)

# L0
esdar <- function(x, y, size=NULL, tau=0.5, intercept=TRUE, normalize=TRUE){
  x <- as.matrix(x)
  y <- as.matrix(y)
  np <- dim(x)
  n <- np[1]
  p <- np[2]
  
  if(intercept){
    meanx <- colMeans(x)
    meany <- sum(y)/n
  }else{
    meanx <- rep(0, p)
    meany <- 0
  }
  x <- scale(x, meanx, FALSE)
  if(normalize){
    normx <- sqrt(colSums(x^2)) 
    sumx2 <- rep(1, p)
  }else{ 
    normx <- rep(1, p)
    sumx2 <- colSums(x^2)
  }
  x <- scale(x, FALSE, normx)
  y <- y - meany
  
  if(is.null(size)) {
    size <- seq(1, ceiling(n/log(n)), 1)
  } 
  tx <- t(x)
  
  sdar <- function(ms){
    bk <- rep(0, p)
    dk <- tx %*% (y - x %*% bk)/sumx2
    Ak <- which(abs(bk+tau*dk) >= sort(abs(bk+tau*dk), decreasing =TRUE)[ms])
    for (k in 1:(2*ms)) {
      Ik <- setdiff(1:p, Ak)
      bk[Ik] <- 0
      bk[Ak] <- solve(tx[Ak ,] %*% x[, Ak]) %*% tx[Ak ,] %*% y
      ek <- y - as.matrix(x[, Ak]) %*% bk[Ak]
      dk[Ak] <- 0
      dk[Ik] <- tx[Ik, ] %*% ek/sumx2[Ik]
      Anew <- which(abs(tau*bk + (1-tau)*dk) >= sort(abs(tau*bk + (1-tau)*dk), decreasing =TRUE)[ms])
      if(setequal(Ak, Anew)){
        return(c(k, bk))
      }
      Ak <- Anew
    }
    return(c(k, bk))
  }
  
  para <- sapply(size, function(ms){sdar(ms)})
  iter <- para[1, ]
  b <- scale(t(para[-1, ]), FALSE, normx)
  esti <- rbind(meany - meanx %*% t(b), t(b))
  
  return(list(beta=esti, size=size, iter=iter))
}
cv.esdar <- function(x, y, size=NULL, tau=0.5, intercept = TRUE, normalize = TRUE, seed=NULL, fold=5){
  x <- as.matrix(x)
  y <- as.matrix(y)
  np <- dim(x)
  n <- np[1]
  p <- np[2]
  
  if(is.null(size)) {size <- seq(1, ceiling(n/log(n)), 1)}
  ##Define group
  leave.out <- trunc(n/fold)
  set.seed(seed)
  o <- sample(1:n)
  groups <- vector("list", fold)
  for (j in 1:(fold - 1)) {
    jj <- (1 + (j - 1) * leave.out)
    groups[[j]] <- (o[jj:(jj + leave.out - 1)])
  }
  groups[[fold]] <- o[(1 + (fold - 1) * leave.out):n]
  
  ##begin CV
  err <- err_sd<- list()
  err_min <- size_min <- 0
  xx <- cbind(1, x)
  for(i in 1:fold){
    xvali  <- xx[groups[[i]], ]
    xtrain <- x[-groups[[i]], ]
    yvali  <- y[groups[[i]]]
    ytrain <- y[-groups[[i]]]
    esti <- esdar(x=xtrain, y=ytrain, size=size, intercept = intercept, normalize = normalize)$beta
    err[[i]] <- (yvali-xvali%*%esti)^2
    err_sd[[i]] <- colMeans(err[[i]])
  }
  pre_err <- colMeans(do.call(rbind, err))
  # pre_sd <- sqrt(rowMeans((do.call(cbind,err_sd)-pre_err)^2)/(fold-1))
  index <- which.min(pre_err)
  # index <- which.min(abs(pre_err-pre_err[index]-pre_sd[index]))
  fit <- esdar(x=x, y=y, size=size[index], intercept = intercept, normalize = normalize)
  esti.opt <- fit$beta
  return(list(beta_opt=esti.opt, size_opt=size[index], size=size, iter_opt=fit$iter))
}

#oracle biased estimator with L0
obe <- function(x, y, para=NULL, size=NULL, intercept=TRUE, normalize=TRUE, tau=0.5, 
                method=c("ridge","liu", "gliu", "sppcr", "gridge")){
  x <- as.matrix(x)
  y <- as.matrix(y)
  np <- dim(x)
  n <- np[1]
  p <- np[2]
  
  if(intercept){ 
    meanx <- colMeans(x)
    meany <- mean(y)
  }else{
    meanx <- rep(0, p)
    meany <- 0
  }
  x <- scale(x, meanx, FALSE)
  y <- y - meany
  if(normalize){
    normx <- sqrt(colSums(x^2)/n) 
    sumx2 <- rep(n, p)
  }else{ 
    normx <- rep(1, p)
    sumx2 <- colSums(x^2)
  }
  x <- scale(x, FALSE, normx)
  tx <- t(x)
  
  if(is.null(size)) {size <- seq(2, ceiling(n/(log(p)*log(n))), 1)}
  
  bk_fun <- function(x, y, para, method="liu"){
    xx <- x/sqrt(n)
    x <- as.matrix(x)
    y <- as.vector(y)
    p <- ncol(x)
    Z <- switch (method,
                 ridge = {sqrt(para)*diag(p)}, 
                 gridge = {SVD <- svd(xx, nv=p); Q <- SVD$v; tQ <- t(Q)
                 if(n>=p){Lambda <- SVD$d^2}else{Lambda <- c(SVD$d^2, rep(0,p-n))}
                 if(length(which(diff(-Lambda) > para))==0){
                   k <- rep(para, p)
                 }else{
                   poi <- max(which(diff(-Lambda) > para))
                   k <- c(rep(0, length(poi)), rep(para, p-length(poi)))
                 }
                 K_sqrt <- diag(sqrt(k))
                 K_sqrt %*% tQ},
                 liu = {SVD <- svd(xx, nv=p); Q <- SVD$v; tQ <- t(Q)
                 Lambda <- SVD$d^2
                 k <- (1-para)*Lambda/(Lambda+para)
                 K_sqrt <- diag(sqrt(k))
                 K_sqrt %*% tQ },
                 gliu = {SVD <- svd(xx, nv=p); Q <- SVD$v; tQ <- t(Q)
                 if(n>=p){Lambda <- SVD$d^2}else{Lambda <- c(SVD$d^2,rep(0,p-n))}
                 k <- (1-para)/(Lambda+2-para)
                 K_sqrt <- diag(sqrt(k))
                 K_sqrt %*% tQ },
                 sppcr = {SVD <- svd(xx, nv=p); Q <- SVD$v; tQ <- t(Q)
                 if(n>=p){Lambda <- SVD$d^2}else{Lambda <- c(SVD$d^2,rep(0,p-n))}
                 r <- max(which(Lambda >= 1))
                 if(r==p){
                   0*diag(p)
                 }else{
                   if(para < min(Lambda)){para <- min(Lambda)}
                   K <- 1/para - Lambda
                   k <- (para-1) / Lambda[1:r]
                   K[1:r] <- (1-para) /(1 + k)  
                   K_sqrt <- diag(sqrt(K))
                   K_sqrt %*% tQ }
                 },
                 
    )
    xnew <- rbind(x, Z*sqrt(n))
    ynew <- c(y, rep(0, p))
    return(list(beta = lm(ynew ~ xnew + 0)$coef, Z=Z))
  }
  
  sdar <- function(ms){
    bk <- rep(0, p)
    gk <- sumx2/n
    dk <- 1/n * tx %*% y/gk
    
    Hk <- sqrt(gk)*abs(tau*bk+(1-tau)*dk)
    Ak <- which(Hk >= sort(Hk, decreasing =TRUE)[ms])
    
    for (k in 1:(2*ms)) {
      Ik <- setdiff(1:p, Ak)
      bk[Ik] <- 0
      fit <- bk_fun(x[, Ak], y, para, method = method)
      bk[Ak] <- fit$beta
      ZAk <- fit$Z
      
      gk[Ak] <- sumx2[Ak]/n + colSums(ZAk^2)
      gk[Ik] <- sumx2[Ik]/n
      
      ek <- (y - x[, Ak] %*% bk[Ak])/n
      dk[Ak] <- 0
      dk[Ik] <- tx[Ik, ] %*% ek /gk[Ik]
      
      Hk <- sqrt(gk)*abs(tau*bk+(1-tau)*dk)
      Anew <- which(Hk >= sort(Hk, decreasing =TRUE)[ms])
      
      if(setequal(Ak, Anew)){
        return(c(k, bk))
      }
      Ak <- Anew
    }
    return(c(k, bk))
  }
  
  para_beta <- sapply(size, function(ms){sdar(ms)})
  iter <- para_beta[1, ]
  b <- scale(t(para_beta[-1, ]), FALSE, normx)
  beta <- rbind(meany - meanx %*% t(b), t(b))
  
  return(list(beta=beta, para = para, size=size, method=method, iter=iter) )
}

cv.obe <- function(x, y, para=NULL, size=NULL, intercept = TRUE, normalize = TRUE, 
                   tau=0.5, seed=NULL, fold=5, method=method){
  x <- as.matrix(x)
  y <- as.matrix(y)
  np <- dim(x)
  n <- np[1]
  p <- np[2]
  if(is.null(para)) {para <- seq(0, 1, 0.1)}
  if(is.null(size)) {size <- seq(2, ceiling(n/log(n)), 1)}
  ##Define group
  leave.out <- trunc(n/fold)
  set.seed(seed)
  o <- sample(1:n)
  groups <- vector("list", fold)
  for (j in 1:(fold - 1)) {
    jj <- (1 + (j - 1) * leave.out)
    groups[[j]] <- (o[jj:(jj + leave.out - 1)])
  }
  groups[[fold]] <- o[(1 + (fold - 1) * leave.out):n]
  
  ##begin CV
  err <- err_sd<- list()
  err_min <- size_min <- 0
  xx <- cbind(1, x)
  for(k in 1:length(para)){
    for(i in 1:fold){
      xvali  <- xx[groups[[i]], ]
      xtrain <- x[-groups[[i]], ]
      yvali  <- y[groups[[i]]]
      ytrain <- y[-groups[[i]]]
      fit <- obe(x=xtrain, y=ytrain, para=para[k], size=size, 
                 intercept = intercept, normalize = normalize, method=method)
      esti <- fit$beta
      err[[i]] <- (yvali-xvali%*%esti)^2
      err_sd[[i]] <- colMeans(err[[i]])
    }
    para_err <- colMeans(do.call(rbind, err)) ##CV
    # d_sd <- sqrt(rowMeans((do.call(cbind,err_sd)-d_err)^2)/(fold-1)) ##1.se
    index <- which.min(para_err)
    # index <- which((d_err-d_err[index]-d_sd[index])<=0) ##1.se
    err_min[k] <- para_err[index]
    size_min[k] <- size[index]
  }
  index <- which.min(err_min)
  fit <- obe(x=x, y=y, para = para[index], size=size_min[index], 
             intercept = intercept, normalize = normalize, method = method)
  esti.opt <- fit$beta
  df <- fit$size
  return(list(beta_opt=esti.opt, para_opt=para[index], size_opt=size_min[index], 
              para=para, size=size, method=method, iter_opt=fit$iter))
}

DGPfun3 <- function(n=200, q=12, p=500, rho=1, sigma=1, R=3, case=1){
  ntrain <- n-100
  minbeta <- sigma*sqrt(2*log(p)/ntrain)
  beta <- rep(0,p)
  poi <- sort(sample(1:p, q))
  beta[poi] <- runif(q, minbeta, R*minbeta)
  X <- xx <- matrix(rnorm(n*p), n, p)
  if(case==1){
    X[, poi[1]] <- xx[, poi[1]]
    for (j in 2:(q-1)) {
      X[, poi[j]] <- xx[, poi[j]] + rho*(xx[, poi[j-1]]+xx[, poi[j+1]])
    }
    repoi <- setdiff(1:p,poi)
    X[, repoi[1]] <- xx[, repoi[1]]
    for (j in 2:(p-q-1)) {
      X[, repoi[j]] <- xx[, repoi[j]] + rho*(xx[, repoi[j-1]]+xx[, repoi[j+1]])
    }
  }else{
    X[, 1] <- xx[, 1]
    for (j in 2:(p-1)) {
      X[, j] <- xx[, j] + rho*(xx[, j-1]+xx[, j+1])
    }
  }
  
  y <- X%*%beta + sigma*rnorm(n)
  Xtrain <- X[1:ntrain, ]
  Xtest <-  X[(ntrain+1):n, ]
  ytrain <- y[1:ntrain]
  ytest <- y[(ntrain+1):n]
  return(list(xtrain=Xtrain, ytrain=ytrain, xtest=Xtest, ytest=ytest, beta=beta))
}


run.example7<- function(aa){
  para <- seq(0.02,0.24,0.02)
  
  ee <- pe<- iter <- pdr <- matrix(0, length(para), 5)
  
  for (i in 1:length(para)) {
    dat <- DGPfun3(n=150, q=12, p=500, rho=0.95, sigma=1, R=3, case=1)
    beta <- dat$beta
    xtrain <- dat$xtrain
    xtest <- dat$xtest
    ytrain <- dat$ytrain
    ytest <- dat$ytest
    
    n <- nrow(xtrain)
    p <- ncol(xtrain)
    
    pos <- which(beta!=0)
    size <- 12
    
    fit.l0 <- esdar(xtrain, ytrain, size=size, tau=0.5, intercept=FALSE)
    beta.l0 <- fit.l0$beta[-1]
    
    fit.oridge <- obe(xtrain, ytrain, para=para[i], intercept = FALSE, size=size, method="ridge")
    beta.oridge<- fit.oridge$beta[-1]
    
    fit.oliu <- obe(xtrain, ytrain, para=1-para[i], intercept = FALSE, size=size, method="liu")
    beta.oliu<- fit.oliu$beta[-1]
    
    fit.oaliu <- obe(xtrain, ytrain, para=1-para[i], intercept = FALSE, size=size, method="gliu")
    beta.oaliu<- fit.oaliu$beta[-1]
    
    
    fit.oaridge <- obe(xtrain, ytrain, para=para[i], intercept = FALSE, size=size, method="gridge")
    beta.oaridge<- fit.oaridge$beta[-1]
    
    ee[i, ] <- c(norm(beta.l0-beta,"2"), norm(beta.oridge-beta,"2"), norm(beta.oliu-beta,"2"),
                 norm(beta.oaliu-beta,"2"),  norm(beta.oaridge-beta,"2"))
    
    pe[i, ] <- c(mean((xtest%*%beta.l0-ytest)^2), mean((xtest%*%beta.oridge-ytest)^2),mean((xtest%*%beta.oliu-ytest)^2),
                 mean((xtest%*%beta.oaliu-ytest)^2),  mean((xtest%*%beta.oaridge-ytest)^2))
    
    iter[i, ] <- c(fit.l0$iter, fit.oridge$iter, fit.oliu$iter, fit.oaliu$iter, fit.oaridge$iter)
    
    pdr[i, ]<-c(length(which(beta.l0[pos]!=0)), length(which(beta.oridge[pos]!=0)), length(which(beta.oliu[pos]!=0)),
                length(which(beta.oaliu[pos]!=0)), length(which(beta.oaridge[pos]!=0)))/length(pos)
  }
  
  
  result <- cbind(ee, pe, iter, pdr)
  colnames(result)<-rep(c("L0", "Oridge", "Oliu", "Oaliu", "Oaridge"), 4)
  rownames(result)<-para
  result 
}

library(snowfall)
library(parallel)
library(ggplot2)
library(RColorBrewer)
library(ggpubr)
####repeat example one###################################
t1<-proc.time()
N <- 100
sfInit(parallel=TRUE,cpus=15)
sfLibrary(MASS)
sfLibrary(matrixStats)
sfExport("DGPfun3")
sfExport("esdar","cv.esdar","obe","cv.obe")
MNFZ<-sfLapply(1:N,run.example7)
sfStop()

#MNFZ
MNJG_mean<-MNJG_sd<-matrix(, nrow(MNFZ[[1]]), ncol(MNFZ[[1]]))
for (i in 1:nrow(MNFZ[[1]])) {
  parai <- t(sapply(MNFZ, function(u){u[i,]}))
  MNJG_mean[i, ] <- colMeans(parai)
  MNJG_sd[i, ] <- colSds(parai)
}


MNJG_mean
MNJG_sd


Aplot <- function(aee, aeesd, yname="AEE"){
  method.names = c("L0", "B-Ridge", "B-Liu", "B-ALiu", "B-ARidge")
  dat = data.frame(para=1:nrow(aee), aee=as.vector(aee), aeesd=as.vector(aeesd), 
                   Method=rep(method.names, each=nrow(aee)))
  fig = ggplot(data=dat, aes(x=para, y=aee, fill=Method, shape=Method, colour=Method, group= Method))+
    # geom_errorbar(aes(ymin=aee-0.1*aeesd, ymax=aee+0.1*aeesd), size=0.5, width=0.2)+
    geom_line(size=0.5) +
    scale_color_manual(values = brewer.pal(5, "Set1"))+ 
    geom_point(size=1, shape = 15, fill=8) +
    scale_x_discrete(limits=factor(1:nrow(aee), labels=seq(0.02,0.24,0.02)))+
    scale_y_log10()+
    theme(panel.background=element_blank(),
          panel.grid.major.y = element_line(colour = "grey",linetype = 2),
          panel.grid.minor.y = element_line(colour = "grey",linetype = 2),
          #axis.text.x = element_text(angle=90, hjust=0, vjust=.4),
          axis.line = element_line(size =rel(1), colour = "black", 
                                   arrow = arrow(angle = 30,length = unit(0.1,"inches"))))+
    theme(legend.position=c(0.93, 0.9), legend.title=element_blank(), 
          legend.text=element_text(size=6), legend.spacing.y=unit(0.1,"lines"))+
    xlab(expression(paste("Turning parameter ",tilde(d)))) + ylab(yname)
  fig
}

p1 <- Aplot(MNJG_mean[,1:5], MNJG_sd[,1:5], yname="AEE")
p2 <- Aplot(MNJG_mean[,6:10], MNJG_sd[,6:10], yname="APE")
p3 <- Aplot(MNJG_mean[,11:15], MNJG_sd[,11:15], yname="Average number of iterations")
p4 <- Aplot(MNJG_mean[,16:20], MNJG_sd[,16:20], yname="APDR")

ggarrange(p1, p2, p3, p4, ncol = 2, nrow = 2, labels=c("(a)","(b)","(c)","(d)"),
          font.label = list(size = 11, color = "black", face = "bold"),
          common.legend = TRUE, legend = "bottom")

