extern crate nalgebra;


use nalgebra::{DMatrix, Dynamic, max, min};
use nalgebra::linalg::SymmetricEigen;
use crate::mean;
use crate::tools::graphToDot;
use crate::tools::saveMatrix;
use crate::tools::calc;
use crate::models::conjectures::invariants;

static GRAPHTYPE: &str = "tree"; //any tree notri girth5
static CONJECTURE: i32 = 10000;
static USE_MINIMAL_MOVES : bool = true;
static SIZE_TERMINAL : usize = 50;
//302 OK 321 OK 289 OK 189 OK 139 OK 290 OK 166 OK
// 284 NO 290 NO 195 NO 21 NO 39 NO 143 NO

#[derive(Clone)]
pub struct State{
    pub adj_mat : DMatrix<f64>,
    pub n_arete: usize,
    pub n_sommet: usize,
    pub seq : Vec<Move>,

    pub min_add_sommet: usize,

    pub stored_score : f64,
    pub stored_score_pertinent : bool
}

impl State{
    pub const CONSIDER_NON_TERM: bool = true; //NMCS marche mieux avec pour la 289

    pub fn new() -> Self {
        Self{ adj_mat: DMatrix::from_diagonal_element(1, 1, 0.0), n_arete: 0, n_sommet: 1, min_add_sommet: 0, seq : Vec::new(), stored_score : 0.0, stored_score_pertinent : false }
    }

    pub fn add_arete(&mut self, from : usize, to : i32){
        if from as i32 != to && self.n_sommet > from  {
            let mut true_to : usize = 0;
            if  to >= self.n_sommet as i32 || to == -1 {
                true_to = self.n_sommet;
                self.n_sommet +=1;
                self.adj_mat.resize_mut(self.n_sommet, self.n_sommet, 0.0)
            }else{
                true_to = to as usize;
                if self.adj_mat[(from, true_to)] != 0.0 {
                    return;
                }
            }
            self.n_arete += 1;
            self.adj_mat[(from, true_to)] = 1.0;
            self.adj_mat[(true_to, from)] = 1.0;
        }
    }

    pub fn play(&mut self, m : Move){
        self.stored_score_pertinent = false;
        self.add_arete(m.from, m.to);
        self.seq.push(m);

        if m.to == -1 {
            self.min_add_sommet = m.from;
        }
    }

    pub fn legal_moves(& self) ->Vec<Move>{

        let mut vec :Vec<Move> = Vec::new();

        if GRAPHTYPE == "any" {
            if USE_MINIMAL_MOVES {
                for j in 0..self.n_sommet-1 {
                    if self.adj_mat[(self.n_sommet-1, j)] == 0.0 {
                        let m1 = Move{ind : self.n_sommet as i32, from : self.n_sommet-1, to : j as i32};
                        vec.push(m1);
                    }
                }
            }else{
                for i in 0..self.n_sommet {
                    for j in i+1..self.n_sommet {
                        if self.adj_mat[(i, j)] == 0.0 {
                            let m1 = Move{ind : self.n_sommet as i32, from : i, to : j as i32};
                            vec.push(m1);
                        }

                    }
                }
            }

        }

        if GRAPHTYPE == "any" || GRAPHTYPE == "tree" || GRAPHTYPE == "notri" || GRAPHTYPE == "girth5" {
            //mode arbre uniquement
            let mut aretesValides = 0;
            if USE_MINIMAL_MOVES {
                aretesValides = self.min_add_sommet;
            }

            for i in aretesValides..self.n_sommet {
                let m1 = Move{
                    ind : self.n_sommet as i32,
                    from : i,
                    to : -1 }; //Move{ from : i, to : self.n_sommet};
                //let m1 = Move{ from : i, to : self.n_sommet as i32 };
                vec.push(m1);
            }
        }

        if GRAPHTYPE == "notri" {
            if USE_MINIMAL_MOVES {
                for j in 0..self.n_sommet-1 {
                    if self.adj_mat[(self.n_sommet-1, j)] == 0.0 {
                        let mut possible = true;

                        for i2 in 0..self.n_sommet {
                            if self.adj_mat[(self.n_sommet-1, i2)] == 1.0 && self.adj_mat[(j, i2)] == 1.0 {
                                possible = false;
                            }
                        }

                        if possible {
                            let m1 = Move{ind : self.n_sommet as i32, from : self.n_sommet-1, to : j as i32};
                            vec.push(m1);
                        }
                    }
                }
            }else{
                for i in 0..self.n_sommet {
                    for j in i+1..self.n_sommet {
                        if self.adj_mat[(i, j)] == 0.0 {
                            let mut possible = true;

                            for i2 in 0..self.n_sommet {
                                if self.adj_mat[(i, i2)] == 1.0 && self.adj_mat[(j, i2)] == 1.0 {
                                    possible = false;
                                }
                            }

                            if possible {
                                let m1 = Move{ind : self.n_sommet as i32, from : i, to : j as i32};
                                vec.push(m1);
                            }
                        }
                    }
                }
            }

        }

        if GRAPHTYPE == "girth5" {
            //peut-être trop couteux ?
            let dist_mat = invariants::dist_matrix(&self.adj_mat);

            if USE_MINIMAL_MOVES {
                for j in 0..self.n_sommet-1 {
                    if self.adj_mat[(self.n_sommet-1, j)] == 0.0 && dist_mat[(self.n_sommet-1, j)] >= 5.0 {
                        let m1 = Move{ind : self.n_sommet as i32, from : self.n_sommet-1, to : j as i32};
                        vec.push(m1);
                    }
                }

            }else{
                for i in 0..self.n_sommet {
                    for j in i..self.n_sommet {
                        if self.adj_mat[(i, j)] == 0.0 && dist_mat[(i, j)] >= 5.0 {
                            let m1 = Move{ind : self.n_sommet as i32, from : i, to : j as i32};
                            vec.push(m1);
                        }
                    }
                }
            }


        }

        return vec;
    }


    pub fn score(&mut self) -> f64{
        if self.n_sommet ==1 {
            return -1.0
        }

        if self.stored_score_pertinent {
            return self.stored_score;
        }



        if CONJECTURE == 302 {

            let eig = SymmetricEigen::new(self.adj_mat.clone());

            let mut max = eig.eigenvalues.max();
            let mut min = eig.eigenvalues.max();
            for e in 0..eig.eigenvalues.len() {
                if eig.eigenvalues[e] < min && eig.eigenvalues[e] > 0.0 {
                    min = eig.eigenvalues[e];
                }
            }

            let SP = max-min;
            let mean_du = invariants::mean_dual(&self.adj_mat);

            if SP - mean_du > 0.0 {
                println!("conjecture 302 résolue {} {} {} {}", SP, mean_du, min, max);
                println!("{}", self.adj_mat);
            }

            self.stored_score = 100.0 + SP - mean_du;
            self.stored_score_pertinent = true;

            return 100.0 + SP - mean_du

        }

        if CONJECTURE == 321 {

            //calculer even vector (nombre de noeuds à distance paire de chaque noeud)
            //moyenne de ça
            //première eigenvalue
            let dist_mat = invariants::dist_matrix(&self.adj_mat);
            let mut even_vec = vec![];
            for i in 0..self.n_sommet {
                even_vec.push(0.0);
                for j in 0..self.n_sommet {
                    if dist_mat[(i, j)]%2.0==0.0 && i!= j{
                        even_vec[i] +=1.0;
                    }
                }
            }
            let mn = mean(&even_vec);

            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let index = eig.eigenvalues.max();

            if index - mn > 0.0 {
                println!("conjecture 321 résolue {} {}", index, mn);
                println!("{}", self.adj_mat);
            }

            self.stored_score = index - mn + 100.0;
            self.stored_score_pertinent = true;

            return index - mn + 100.0

        }

        if CONJECTURE == 289 {
            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut index = eig.eigenvalues.min();
            let mut lambda2 = eig.eigenvalues.min();
            for e in 0..self.n_sommet {
                if eig.eigenvalues[e] > lambda2 {
                    if eig.eigenvalues[e] > index {
                        lambda2 = index;
                        index = eig.eigenvalues[e];
                    }else{
                        lambda2 = eig.eigenvalues[e];
                    }
                }
            }

            let mean_du = invariants::mean_dual(&self.adj_mat);
            if lambda2 - mean_du > 0.0 {
                println!("conjecture 289 résolue {} {}", lambda2, mean_du);
                println!("{}", self.adj_mat);
            }

            self.stored_score = lambda2 - mean_du + 100.0;
            self.stored_score_pertinent = true;

            return lambda2 - mean_du + 100.0
        }

        if CONJECTURE == 284 {

            if self.n_sommet < 3 {return 0.0}

            let dist_mat = invariants::dist_matrix(&self.adj_mat);
            let eig = SymmetricEigen::new(dist_mat);
            let min_du = invariants::min_dual(&self.adj_mat);

            if min_du + eig.eigenvalues.min() > 0.0 {
                println!("conjecture 284 résolue {} {}", eig.eigenvalues.min(), min_du);
                println!("{}", self.adj_mat);
            }

            self.stored_score = min_du + eig.eigenvalues.min() + 100.0;
            self.stored_score_pertinent = true;

            return min_du + eig.eigenvalues.min() + 100.0
        }

        if CONJECTURE == 290 {
            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut lambda_n = eig.eigenvalues.max();
            let mut lambda_n_1 = eig.eigenvalues.max();

            for e in 0..self.n_sommet {
                if eig.eigenvalues[e] < lambda_n_1 {
                    if eig.eigenvalues[e] < lambda_n {
                        lambda_n_1 = lambda_n;
                        lambda_n = eig.eigenvalues[e];
                    }else{
                        lambda_n_1 = eig.eigenvalues[e];
                    }
                }
            }
            let grav_mat = invariants::gravity_matrix(&self.adj_mat);
            let mean_grav = grav_mat.mean();

            if - lambda_n_1 - (self.n_arete as f64)/mean_grav > 0.0 {
                println!("conjecture 290 résolue {} {} {} {}", lambda_n_1, lambda_n, (self.n_arete as f64)/mean_grav, self.n_arete );
                println!("{}", eig.eigenvalues);
                println!("{}", self.adj_mat);
                println!("{}", grav_mat);

                std::process::exit(123);

            }

            self.stored_score = - lambda_n_1 - (self.n_arete as f64)/mean_grav + 1000.0;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return - lambda_n_1 - (self.n_arete as f64)/mean_grav + 1000.0
        }

        if CONJECTURE == 189 {

            if !self.terminal() && false {

                let crasher = vec![0.0];
                let bug = crasher[5];
            }

            let lap = invariants::laplacian_matrix(&self.adj_mat);
            let lap_eigen = SymmetricEigen::new(lap);
            let mut vec_eigen = vec![];

            for e in  0..self.n_sommet {
                vec_eigen.push(lap_eigen.eigenvalues[e]);
            }

            let m = invariants::mode(vec_eigen);

            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut p_minus = vec![];

            for e in  0..self.n_sommet {
                if eig.eigenvalues[e] <= 0.0000000001 {
                    p_minus.push(eig.eigenvalues[e]);
                }
            }



            if m - (p_minus.len() as f64) > 0.00001 {
                let mut pair : f64 = invariants::even_vec(&self.adj_mat).iter().sum();
                let mut odd : f64 = invariants::odd_vec(&self.adj_mat).iter().sum();
                if odd <= pair {
                    println!("conjecture 189 résolue {} {} ", m, p_minus.len());


                    println!("{}, {}", pair, odd);
                    println!("adj eigen {}", eig.eigenvalues);
                    println!("lap eigen {}", lap_eigen.eigenvalues);
                    println!("{}", self.adj_mat);
                }

            }

            self.stored_score = m-(p_minus.len() as f64) + 100.0;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return m-(p_minus.len() as f64) + 100.0

        }

        if CONJECTURE == 195 {

            if !self.terminal() && false {

                let crasher = vec![0.0];
                let bug = crasher[5];
            }

            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let index = eig.eigenvalues.max();

            let ev = invariants::even_vec(&self.adj_mat);
            let mut max_ev = ev[0];
            for e in ev {
                if e > max_ev {
                    max_ev = e;
                }
            }

            let mut pair : f64 = invariants::even_vec(&self.adj_mat).iter().sum();
            let mut odd : f64 = invariants::odd_vec(&self.adj_mat).iter().sum();

            let mut ratio =  if pair >= odd {1.0} else {pair/odd};
            //ratio = 1.0;

            if index - max_ev > 0.0 {
                if odd <= pair {
                    println!("conjecture 195 résolue {} {} ", index, max_ev);

                    println!("{}, {}", pair, odd);
                    println!("{}", self.adj_mat);
                }else{
                    //println!("conjecture 195 pas tout à  fait résolue {} {} ", index, max_ev);

                    //println!("{}, {}", pair, odd);
                    //println!("{}", self.adj_mat);
                }

            }

            self.stored_score = (index - max_ev + 100.0)*ratio;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return (index - max_ev + 100.0)*ratio

        }

        if CONJECTURE == 166 {

            //pour le GBFS, il doit y avoir un minimum local ?
            //if self.n_sommet < 3 {return 0.0}

            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut p_minus = vec![];

            for e in  0..self.n_sommet {
                if eig.eigenvalues[e] <= 0.0000000000001 {
                    p_minus.push(eig.eigenvalues[e]);
                }
            }



            let sqrt_m = (self.n_arete as f64).sqrt();

            if sqrt_m - (p_minus.len() as f64) > 0.0 {
                println!("conjecture 166 résolue {} {} ", sqrt_m, p_minus.len());
                println!("{}", self.adj_mat);
            }

            self.stored_score = sqrt_m - (p_minus.len() as f64) + 100.0;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return sqrt_m - (p_minus.len() as f64) + 100.0

        }

        if CONJECTURE == 139 {

            //pour le GBFS, il doit y avoir un minimum local ?
            //if self.n_sommet < 3 {return 0.0}

            let eig = SymmetricEigen::new(self.adj_mat.clone());


            let mut smallest_eigen = eig.eigenvalues.max();
            let mut second_smallest_eigen = eig.eigenvalues.max();

            for e in 0..self.n_sommet {
                if eig.eigenvalues[e] < second_smallest_eigen {
                    if eig.eigenvalues[e] < smallest_eigen {
                        second_smallest_eigen = smallest_eigen;
                        smallest_eigen = eig.eigenvalues[e];
                    }else{
                        second_smallest_eigen = eig.eigenvalues[e];
                    }
                }
            }

            let harmonic = invariants::harmonic(&self.adj_mat.clone());

            if -harmonic - second_smallest_eigen > 0.0 {
                println!("conjecture 139 résolue {} {} ", harmonic, second_smallest_eigen);
                println!("{}", self.adj_mat);

                graphToDot::adj_matrix_to_dot(self.adj_mat.clone(), "graffiti139");
                saveMatrix::save_matrix("adjGraffiti139", self.adj_mat.clone());

                std::process::exit(123);

            }

            self.stored_score = -harmonic - second_smallest_eigen + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return -harmonic - second_smallest_eigen + 100.0;

        }

        if CONJECTURE == 21 {

            //pour le GBFS, il doit y avoir un minimum local ?
            if self.n_sommet < 3 {return 0.0}

            //let dist_mat = invariants::dist_matrix(&self.adj_mat);
            let eig = SymmetricEigen::new(self.adj_mat.clone());
            //et eigDist = SymmetricEigen::new(dist_mat.clone());
            let mut num_eig_neg = 0.0;
            let mut sum_eig_pos = 0.0;

            for e in 0..eig.eigenvalues.len() {
                if eig.eigenvalues[e] < -0.0001 {
                    num_eig_neg += 1.0;
                }
            }
            for e in 0..eig.eigenvalues.len() {
                if eig.eigenvalues[e] > 0.0001 {
                    sum_eig_pos += eig.eigenvalues[e];
                }
            }



            if num_eig_neg - sum_eig_pos > 0.00001 {
                println!("conjecture 21 résolue {} {} ", num_eig_neg, sum_eig_pos);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = num_eig_neg - sum_eig_pos + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return num_eig_neg - sum_eig_pos + 100.0;

        }

        if CONJECTURE == 39 {

            //deviaition of distance matrix is not more than the number of positive eigenvalues
            //if self.n_sommet < 5 {return 0.0}


            let dist_mat = invariants::dist_matrix(&self.adj_mat);
            let mut vecDist = Vec::new();
            for i in 0..self.n_sommet {
                for j in 0..self.n_sommet
                {
                    vecDist.push(dist_mat[(i, j)]);
                }
            }
            let dev = invariants::std_dev(vecDist);


            let eig = SymmetricEigen::new(self.adj_mat.clone());
            //et eigDist = SymmetricEigen::new(dist_mat.clone());
            let mut num_eig_pos = 0.0;

            for e in 0..eig.eigenvalues.len() {
                if eig.eigenvalues[e] > 0.0001 {
                    num_eig_pos += 1.0;
                }
            }




            if dev - num_eig_pos > 0.00001 {
                println!("conjecture 39 résolue {} {} ", dev, num_eig_pos);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = dev - num_eig_pos + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return dev - num_eig_pos + 100.0;

        }

        if CONJECTURE == 40 {

            //deviaition of distance matrix is not more than the number of negative eigenvalues
            //if self.n_sommet < 5 {return 0.0}


            let dist_mat = invariants::dist_matrix(&self.adj_mat);
            let mut vecDist = Vec::new();
            for i in 0..self.n_sommet {
                for j in 0..self.n_sommet
                {
                    vecDist.push(dist_mat[(i, j)]);
                }
            }
            let dev = invariants::std_dev(vecDist);


            let eig = SymmetricEigen::new(self.adj_mat.clone());
            //et eigDist = SymmetricEigen::new(dist_mat.clone());
            let mut num_eig_neg = 0.0;

            for e in 0..eig.eigenvalues.len() {
                if eig.eigenvalues[e] < -0.0001 {
                    num_eig_neg += 1.0;
                }
            }




            if dev - num_eig_neg > 0.00001 {
                println!("conjecture 40 résolue {} {} ", dev, num_eig_neg);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = dev - num_eig_neg + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return dev - num_eig_neg + 100.0;

        }

        if CONJECTURE == 143 {

            //variance eigen positives <= nb aretes/distance moyenne


            let dist_mat = invariants::dist_matrix(&self.adj_mat);
            let mut vecDist = Vec::new();
            for i in 0..self.n_sommet {
                for j in 0..self.n_sommet
                {
                    vecDist.push(dist_mat[(i, j)]);
                }
            }
            let mean_dist = invariants::mean(vecDist);


            let eig = SymmetricEigen::new(self.adj_mat.clone());
            //et eigDist = SymmetricEigen::new(dist_mat.clone());
            let mut eig_pos = vec![];

            for e in 0..eig.eigenvalues.len() {
                if eig.eigenvalues[e] > 0.0001 {
                    eig_pos.push(eig.eigenvalues[e]);
                }
            }

            let mut v = invariants::std_dev(eig_pos);
            v =v*v;


            if v - (self.n_arete as f64)/mean_dist > 0.00001 {
                println!("conjecture 143 résolue {} {} ", v, (self.n_arete as f64)/mean_dist);
                println!("{}", self.adj_mat);
            }

            self.stored_score = v - (self.n_arete as f64)/mean_dist + 1000.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return v - (self.n_arete as f64)/mean_dist + 1000.0;

        }

        if CONJECTURE == 145 {

            //minimum derivative eigenpos <= nb sommets/distance moyenne


            let dist_mat = invariants::dist_matrix(&self.adj_mat);
            let mut vecDist = Vec::new();
            for i in 0..self.n_sommet {
                for j in 0..self.n_sommet
                {
                    vecDist.push(dist_mat[(i, j)]);
                }
            }
            let mean_dist = invariants::mean(vecDist);


            let eig = SymmetricEigen::new(self.adj_mat.clone());
            //et eigDist = SymmetricEigen::new(dist_mat.clone());
            let mut eig_pos = vec![];

            for e in 0..eig.eigenvalues.len() {
                if eig.eigenvalues[e] > 0.0001 {
                    eig_pos.push(eig.eigenvalues[e]);
                }
            }

            if(eig_pos.len() < 2){
                return 0.0;
            }

            eig_pos.sort_by(|a, b| a.partial_cmp(b).unwrap());

            let der = invariants::vec_derivative(eig_pos);
            let mut min_der = der[0];
            for i in 0..der.len() {
                if min_der > der[i] {
                    min_der = der[i];
                }
            }


            if min_der - (self.n_sommet as f64)/mean_dist > 0.00001 {
                println!("conjecture 39 résolue {} {} ", min_der, (self.n_sommet as f64)/mean_dist);
                println!("{}", self.adj_mat);
            }

            self.stored_score = min_der - (self.n_sommet as f64)/mean_dist + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return min_der - (self.n_sommet as f64)/mean_dist + 100.0;

        }

        if CONJECTURE == 154 {

            //dev eigen <= nb sommet/distance moyenne


            let dist_mat = invariants::dist_matrix(&self.adj_mat);
            let mut vecDist = Vec::new();
            for i in 0..self.n_sommet {
                for j in 0..self.n_sommet
                {
                    vecDist.push(dist_mat[(i, j)]);
                }
            }
            let mean_dist = invariants::mean(vecDist);


            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut eigvec = vec![];
            for e in 0..eig.eigenvalues.len() {
                eigvec.push(eig.eigenvalues[e]);
            }

            let mut stdev = invariants::std_dev(eigvec);


            if stdev - (self.n_sommet as f64)/mean_dist > 0.00001 {
                println!("conjecture 39 résolue {} {} ", stdev, (self.n_sommet as f64)/mean_dist);
                println!("{}", self.adj_mat);
            }

            self.stored_score = stdev - (self.n_sommet as f64)/mean_dist + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return stdev - (self.n_sommet as f64)/mean_dist + 100.0;

        }

        if CONJECTURE == 715 {

            //max(non positive eigen) - min(non positive eigen) <= moy(degree vertex dont le degree est > moyenne des degree)


            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut nonposeigvec = vec![];
            for e in 0..eig.eigenvalues.len() {
                if eig.eigenvalues[e] <= 0.0 {
                    nonposeigvec.push(eig.eigenvalues[e]);
                }
            }

            let sp = nonposeigvec.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b)) - nonposeigvec.iter().fold(f64::INFINITY, |a, &b| a.min(b));

            let mut moy = self.adj_mat.sum()/(self.adj_mat.row(0).len() as f64);
            let mut moy2 = 0.0;
            let mut nmoy2 = 0.0;
            for i in 0..self.adj_mat.row(0).len() {
                let deg = self.adj_mat.row(i).sum();
                if deg > moy {
                    moy2 += deg;
                    nmoy2 += 1.0;
                }
            }
            moy2 = moy2/nmoy2;

            if sp - moy2 > 0.00001 {
                println!("conjecture 715 résolue {} {} {:?} ", sp, moy2, nonposeigvec);
                println!("{}", self.adj_mat);
            }

            self.stored_score = sp - moy2 + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return sp - moy2 + 100.0;

        }

        if CONJECTURE == 20 {

            //nb pos eigenvalues <= sum pos eigenvalues


            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut poseigvec = vec![];
            for e in 0..eig.eigenvalues.len() {
                if eig.eigenvalues[e] > 0.000000000000001 {
                    poseigvec.push(eig.eigenvalues[e]);
                }
            }

            let coun = poseigvec.len() as f64;
            let mut su = 0.0;
            for f in &poseigvec {
                su += f;
            }

            if coun - su > 0.00001 {
                println!("conjecture 20 résolue {} {} {:?} ", coun, su, poseigvec);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = coun - su + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return coun - su + 100.0;

        }

        if CONJECTURE == 254 {

            //min deriv laplacien <= somme 1/nb vertice odd distance

            let laplacien = invariants::laplacian_matrix(&self.adj_mat);
            let eig = SymmetricEigen::new(laplacien);
            let mut sorted_vec = vec![];
            for e in 0..eig.eigenvalues.len() {
                sorted_vec.push(eig.eigenvalues[e]);
            }
            sorted_vec.sort_by(|a, b| a.partial_cmp(b).unwrap());
            let deriv = invariants::vec_derivative(sorted_vec);
            let mut min_deriv = f64::INFINITY;
            for e in deriv {
                if e < min_deriv {
                    min_deriv = e;
                }
            }

            let dist_mat = invariants::dist_matrix(&self.adj_mat);
            let mut sum : f64 = 0.0;
            for i in 0..self.adj_mat.row(0).len() {
                let mut nb_at_odd_dist = 0.0;
                for j in 0..self.adj_mat.row(0).len() {
                    if dist_mat[(i, j)] as i32 % 2 == 1 {
                        nb_at_odd_dist += 1.0;
                    }
                }
                sum += 1.0/nb_at_odd_dist;
            }

            if min_deriv - sum > 0.0{
                println!("conjecture 245 résolue {} {} ", min_deriv, sum);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = min_deriv - sum + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return min_deriv - sum + 100.0;

        }

        if CONJECTURE == 262 {

            //- index <= max(ev)

            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let index = eig.eigenvalues.max();

            let ev = invariants::even_vec(&self.adj_mat);
            let mut max_ev = ev[0];
            for e in ev {
                if e > max_ev {
                    max_ev = e;
                }
            }


            if -index - max_ev > 0.0{
                println!("conjecture 262 résolue {} {} ", index, max_ev);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = -index - max_ev + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return -index - max_ev + 100.0;

        }

        if CONJECTURE == 244 { //clique 4 free graph only

            // dev(eigen(laplacien) <= n_sommet/2

            let laplacien = invariants::laplacian_matrix(&self.adj_mat);
            let eig = SymmetricEigen::new(laplacien);
            let mut eigvec = vec![];
            for e in 0..eig.eigenvalues.len() {
                eigvec.push(eig.eigenvalues[e]);
            }
            let dev = invariants::std_dev(eigvec);


            if dev - (self.n_sommet as f64)/2.0 > 0.0{
                println!("conjecture 244 résolue {} {} ", dev, (self.n_sommet as f64)/2.0);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = dev - (self.n_sommet as f64)/2.0  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return dev - (self.n_sommet as f64)/2.0  + 100.0;

        }

        if CONJECTURE == 209 {

            // eigen strict pos <= mean(sum(columns(distmat)))

            let dist_mat = invariants::dist_matrix(&self.adj_mat);
            let mut t = vec![];
            for i in 0..self.adj_mat.row(0).len() {
                let mut column_sum = 0.0;
                for j in 0..self.adj_mat.row(0).len() {
                    column_sum += dist_mat[(i, j)];
                }
                t.push(column_sum)
            }
            let mean_t = calc::mean(&t);

            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut sum_eig_pos = 0.0;
            for e in 0..eig.eigenvalues.len() {
                if eig.eigenvalues[e] > 0.0001 {
                    sum_eig_pos += eig.eigenvalues[e];
                }
            }

            if sum_eig_pos - mean_t > 0.0001{
                let mut pair : f64 = invariants::even_vec(&self.adj_mat).iter().sum();
                let mut odd : f64 = invariants::odd_vec(&self.adj_mat).iter().sum();
                if pair <= odd {
                    println!("conjecture 209 résolue {} {} ", sum_eig_pos, mean_t);
                    println!("{}", self.adj_mat);
                    std::process::exit(123);
                }
            }

            self.stored_score = sum_eig_pos - mean_t  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return sum_eig_pos - mean_t  + 100.0;

        }

        if CONJECTURE == 712 {

            // min(tp) <= nb eigen (<=) 0
            //tp = d(v)/(n-d(v)

            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut nonposeigvec = 0.0;
            for e in 0..eig.eigenvalues.len() {
                if eig.eigenvalues[e] <= 0.00001 {
                    nonposeigvec += 1.0;
                }
            }

            let temp_vec = invariants::temperature_vec(&self.adj_mat);
            let mut min_temp = f64::INFINITY;
            for e in temp_vec {
                if e < min_temp {
                    min_temp = e;
                }
            }

            if min_temp - nonposeigvec > 0.0001{
                println!("conjecture 712 résolue {} {} ", min_temp, nonposeigvec);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = min_temp - nonposeigvec  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return min_temp - nonposeigvec  + 100.0;

        }

        if CONJECTURE == 197 {

            // - seconde plus petite eigen <= nb valeur distincte eigen gravity

            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut lambda_n = eig.eigenvalues.max();
            let mut lambda_n_1 = eig.eigenvalues.max();

            for e in 0..self.n_sommet {
                if eig.eigenvalues[e] < lambda_n_1 {
                    if eig.eigenvalues[e] < lambda_n {
                        lambda_n_1 = lambda_n;
                        lambda_n = eig.eigenvalues[e];
                    }else{
                        lambda_n_1 = eig.eigenvalues[e];
                    }
                }
            }
            let grav_mat = invariants::gravity_matrix(&self.adj_mat);
            let eig_grav = SymmetricEigen::new(grav_mat.clone());
            let rank = eig_grav.eigenvalues.max() - eig_grav.eigenvalues.min();
            /*
            let mut eig_grav_vec = vec![];
            for e in 0..eig_grav.eigenvalues.len() {
                eig_grav_vec.push(eig_grav.eigenvalues[e]);
            }
            let rank = invariants::vec_rank(eig_grav_vec);

             */


            if - lambda_n_1 - rank > 0.0001{
                let mut pair : f64 = invariants::even_vec(&self.adj_mat).iter().sum();
                let mut odd : f64 = invariants::odd_vec(&self.adj_mat).iter().sum();
                if odd <= pair {
                    println!("conjecture 197 résolue {} {} ", lambda_n_1, rank);
                    println!("{}", self.adj_mat);
                    //println!("{}", grav_mat);

                    //std::process::exit(123);
                }
            }

            self.stored_score = - lambda_n_1 - rank  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return - lambda_n_1 - rank  + 100.0;

        }

        if CONJECTURE == 198 {

            // - seconde plus petite eigen <= nb valeur distincte eigen gravity

            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let min_eig = eig.eigenvalues.min();

            let mean_grav = invariants::gravity_matrix(&self.adj_mat).mean();


            if min_eig - (self.n_sommet as f64)/mean_grav > 0.0001{
                let mut pair : f64 = invariants::even_vec(&self.adj_mat).iter().sum();
                let mut odd : f64 = invariants::odd_vec(&self.adj_mat).iter().sum();
                if odd <= pair {
                    println!("conjecture 198 résolue {} {} ", min_eig, (self.n_sommet as f64)/mean_grav);
                    println!("{}", self.adj_mat);
                    std::process::exit(123);
                }
            }

            self.stored_score = min_eig - (self.n_sommet as f64)/mean_grav  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return min_eig - (self.n_sommet as f64)/mean_grav  + 100.0;

        }

        if CONJECTURE == 28 {

            // randic index <= sum eigen pos

            if true {


                //star -> index = sqrt(n-1)
                //star + queue -> index = sqrt(n-1)
                let starsize = 1500;
                let queuesize = 1;

                let size = 1+starsize + queuesize;
                let mut verif = DMatrix::from_diagonal_element(size, size, 0.0);


                for i in 1..starsize {

                    verif[(0,i)] = 1.0;
                    verif[(i,0)] = 1.0;


                }

                //verif[(starsize-3,starsize-2)] = 1.0;
                //verif[(starsize-2,starsize-3)] = 1.0;

                //verif[(starsize-5,starsize-4)] = 1.0;
                //verif[(starsize-4,starsize-5)] = 1.0;

                for i in 0..queuesize {
                    verif[(starsize-1 + i,starsize + i)] = 1.0;
                    verif[(starsize + i,starsize-1 + i)] = 1.0;
                }

                //verif[(starsize + queuesize -1, 1)] = 1.0;
                //verif[(1,starsize + queuesize -1)] = 1.0;


                //println!("{}", verif);
                self.adj_mat = verif;
                graphToDot::adj_matrix_to_dot(self.adj_mat.clone(), "graffiti28TEST");

            }

            let randic = invariants::randic_index(&self.adj_mat);


            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut sum_eig_pos = 0.0;
            let mut eig_pos = vec![];
            for e in 0..eig.eigenvalues.len() {
                if eig.eigenvalues[e] > 0.0001 {
                    sum_eig_pos += eig.eigenvalues[e];
                    eig_pos.push(eig.eigenvalues[e]);
                }
            }

            if randic - sum_eig_pos > -0.000001 && randic - sum_eig_pos < 0.000001 {
                sum_eig_pos = sum_eig_pos +1.0;
            }

            if self.n_sommet%5==0 {
                let name = format!("graffiti28size{}", self.n_sommet);
                graphToDot::adj_matrix_to_dot(self.adj_mat.clone(), name.as_str());
                saveMatrix::save_matrix(name.as_str(), self.adj_mat.clone());
            }


            if randic - sum_eig_pos > 0.0001{
                println!("conjecture 28 résolue {} {} ", randic, sum_eig_pos);
                println!("{}", self.adj_mat);
                println!("{}", eig.eigenvalues);

                graphToDot::adj_matrix_to_dot(self.adj_mat.clone(), "graffiti28");
                saveMatrix::save_matrix("graffiti28", self.adj_mat.clone());

                std::process::exit(123);
            }
            println!("score : {}", randic - sum_eig_pos);
            println!("score : {}", randic - sum_eig_pos);
            println!("randic : {}", randic);
            println!("index : {}", eig.eigenvalues.max());
            println!("eig pos : {:?}", eig_pos);


            std::process::exit(123);

            self.stored_score = randic - sum_eig_pos  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return randic - sum_eig_pos  + 100.0;

        }

        if CONJECTURE == 29 {

            // randic index <= nb eign neg
            let randic = invariants::randic_index(&self.adj_mat);

            let dist_mat = invariants::dist_matrix(&self.adj_mat);
            let eig_dist = SymmetricEigen::new(dist_mat);
            let mut nb_eig_neg = 0.0;
            for e in 0..eig_dist.eigenvalues.len() {
                if eig_dist.eigenvalues[e] < -0.0001 {
                    nb_eig_neg += 1.0;
                }
            }


            if randic - nb_eig_neg > 0.0001{
                println!("conjecture 29 résolue {} {} ", randic, nb_eig_neg);
                println!("{}", self.adj_mat);
                println!("{}", eig_dist.eigenvalues);

                graphToDot::adj_matrix_to_dot(self.adj_mat.clone(), "graffiti29");
                saveMatrix::save_matrix("adjGraffiti29", self.adj_mat.clone());

                std::process::exit(123);

            }

            self.stored_score = randic - nb_eig_neg  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return randic - nb_eig_neg  + 100.0;

        }

        if CONJECTURE == 30 {

            // nb eig pos distance <= sum temp

            let dist_mat = invariants::dist_matrix(&self.adj_mat);
            let eig_dist = SymmetricEigen::new(dist_mat);
            let mut nb_eig_pos = 0.0;
            for e in 0..eig_dist.eigenvalues.len() {
                if eig_dist.eigenvalues[e] > 0.0001 {
                    nb_eig_pos += 1.0;
                }
            }

            let temp = invariants::temperature_vec(&self.adj_mat);
            let mut sum_temp = 0.0;
            for t in temp {
                sum_temp += t;
            }

            if nb_eig_pos - sum_temp > 0.0001{
                println!("conjecture 30 résolue {} {} ", nb_eig_pos, sum_temp);
                println!("{}", self.adj_mat);

                graphToDot::adj_matrix_to_dot(self.adj_mat.clone(), "graffiti30");
                saveMatrix::save_matrix("adjGraffiti30", self.adj_mat.clone());

                std::process::exit(123);
            }

            self.stored_score = nb_eig_pos - sum_temp  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return nb_eig_pos - sum_temp  + 100.0;

        }

        if CONJECTURE == 301 {

            // scope eigen pos <= harmonique
            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut smallest_positive = f64::INFINITY;
            let mut largest_positive = 0.0;

            for i in 0..eig.eigenvalues.len() {

                if eig.eigenvalues[i] > largest_positive {
                    largest_positive = eig.eigenvalues[i];
                }
                if eig.eigenvalues[i] < smallest_positive && eig.eigenvalues[i] > 0.0000001 {
                    smallest_positive =eig.eigenvalues[i];
                }
            }

            let scope = largest_positive - smallest_positive;

            let harmonic = invariants::harmonic(&self.adj_mat);


            if scope - harmonic > 0.0001{
                println!("conjecture 301 résolue {} {} ", scope, harmonic);
                println!("{}", self.adj_mat);
                println!("{}", eig.eigenvalues);

                graphToDot::adj_matrix_to_dot(self.adj_mat.clone(), "graffiti301");
                saveMatrix::save_matrix("adjGraffiti301", self.adj_mat.clone());

                std::process::exit(123);

            }

            self.stored_score = scope - harmonic  + 100.0;;
            self.stored_score_pertinent = true;

            //println!("{}", self.stored_score);

            return scope - harmonic  + 100.0;

        }

        if CONJECTURE == 137 {

            // lambda2 <= harmonique
            /*
            //p = 2*sqrt(q)
            let n = 9;
            let p = n * 2; //4
            let q = n*n; //4
            let size = p+2+q;
            let mut verif = DMatrix::from_diagonal_element(size, size, 0.0);
            for i in 0..size {
                for j in 0..size {
                    if i!=j {
                        if i< p && j < p {
                            verif[(i, j)] = 1.0;
                        }

                        if i == p {
                            verif[(i, j)] = 1.0;
                        }
                        if j == p {
                            verif[(i, j)] = 1.0;
                        }

                        if i == p+1 && j > p {
                            verif[(i, j)] = 1.0;
                        }
                        if j == p+1 && i > p {
                            verif[(i, j)] = 1.0;
                        }
                    }
                }
            }
            //println!("{}", verif);
            self.adj_mat = verif;
            */


            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut index = eig.eigenvalues.min();
            let mut lambda2 = eig.eigenvalues.min();
            for e in 0..self.n_sommet {
                if eig.eigenvalues[e] > lambda2 {
                    if eig.eigenvalues[e] > index {
                        lambda2 = index;
                        index = eig.eigenvalues[e];
                    }else{
                        lambda2 = eig.eigenvalues[e];
                    }
                }
            }

            let harmonic = invariants::harmonic(&self.adj_mat);


            if lambda2 - harmonic > 0.0001{
                println!("conjecture 137 résolue {} {} ", lambda2, harmonic);
                println!("{}", self.adj_mat);
                println!("{}", eig.eigenvalues);

                graphToDot::adj_matrix_to_dot(self.adj_mat.clone(), "graffiti137");
                saveMatrix::save_matrix("adjGraffiti137", self.adj_mat.clone());

                std::process::exit(123);

            }else{
                //println!("nooon {}", lambda2 - harmonic  + 100.0);
            }

            self.stored_score = lambda2 - harmonic  + 100.0;
            self.stored_score_pertinent = true;

            //println!("{}", self.stored_score);

            return lambda2 - harmonic  + 100.0;

        }

        if CONJECTURE == 140 {

            // stddev eigen <= harmonique



            //p = 2*sqrt(q)
            let n = 15;
            let p = n * 2;
            let q = n*n;
            let size = p+2+q;
            let mut verif = DMatrix::from_diagonal_element(size, size, 0.0);
            for i in 0..size {
                for j in 0..size {
                    if i!=j {
                        if i< p && j < p {
                            verif[(i, j)] = 1.0;
                        }

                        if i == p {
                            verif[(i, j)] = 1.0;
                        }
                        if j == p {
                            verif[(i, j)] = 1.0;
                        }

                        if i == p+1 && j > p {
                            verif[(i, j)] = 1.0;
                        }
                        if j == p+1 && i > p {
                            verif[(i, j)] = 1.0;
                        }
                    }
                }
            }
            //println!("{}", verif);
            //self.adj_mat = verif;





            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut eig_vec = vec![];
            for e in 0..eig.eigenvalues.len(){
                eig_vec.push(eig.eigenvalues[e]);
            }
            let dev = invariants::std_dev(eig_vec);

            let mut harmonic = invariants::harmonic(&self.adj_mat);

            if dev - harmonic > -0.000001 && dev - harmonic < 0.000001 {
                harmonic = harmonic +1.0;
            }

            if dev - harmonic > 0.0001{
                println!("conjecture 140 résolue {} {} ", dev, harmonic);
                println!("{}", self.adj_mat);
                println!("{}", eig.eigenvalues);

                std::process::exit(123);

            }

            //println!("score : {}", dev - harmonic  + 100.0);
            //std::process::exit(123);

            self.stored_score = dev - harmonic  + 100.0;
            self.stored_score_pertinent = true;

            //println!("{}", self.stored_score);

            return dev - harmonic  + 100.0;

        }

        if CONJECTURE == 714 {

            //- moyenne nonpos eigen <= sum 1/temp

            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut nonposeigvec = 0.0;
            let mut n = 0.0;
            for e in 0..eig.eigenvalues.len() {
                if eig.eigenvalues[e] <= 0.00001 {
                    nonposeigvec += eig.eigenvalues[e];
                    n += 1.0;
                }
            }
            let moy = nonposeigvec/n;

            let temp_vec = invariants::temperature_vec(&self.adj_mat);
            let mut sum_inv_temp = 0.0;
            for e in temp_vec {
                sum_inv_temp += 1.0/e;
            }

            if -moy - sum_inv_temp > 0.0001{
                println!("conjecture 714 résolue {} {} ", moy, sum_inv_temp);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = -moy - sum_inv_temp  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return -moy - sum_inv_temp  + 100.0;

        }

        if CONJECTURE == 219 {

            // seconde eigen gravmat <= n*(n-1)/2-m


            let eig = SymmetricEigen::new(invariants::gravity_matrix(&self.adj_mat));
            let mut index = eig.eigenvalues.min();
            let mut lambda2 = eig.eigenvalues.min();
            for e in 0..self.n_sommet {
                if eig.eigenvalues[e] > lambda2 {
                    if eig.eigenvalues[e] > index {
                        lambda2 = index;
                        index = eig.eigenvalues[e];
                    }else{
                        lambda2 = eig.eigenvalues[e];
                    }
                }
            }

            let other = self.n_sommet as f64*(self.n_sommet as f64-1.0)/2.0 - self.n_arete as f64;

            if lambda2 - other > 0.0001{
                println!("conjecture 219 résolue {} {} ", lambda2, other);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = lambda2 - other  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return lambda2 - other  + 100.0;

        }

        if CONJECTURE == 322 {

            // sum inv even vec<= rang eig distmat

            let eig = SymmetricEigen::new(invariants::dist_matrix(&self.adj_mat));

            let mut eig_vec = vec![];
            for e in 0..eig.eigenvalues.len(){
                eig_vec.push(eig.eigenvalues[e]);
            }

            //let rank_dist = invariants::vec_rank(eig_vec);



            let scope = eig.eigenvalues.max() - eig.eigenvalues.min();
            let rank_dist = scope;


            let even_vec = invariants::even_vec(&self.adj_mat);
            let mut inv_even = 0.0;
            for i in even_vec {
                if i != 0.0 {
                    inv_even += 1.0/i;
                }

            }

            if inv_even - rank_dist > 0.0001{
                println!("conjecture 322 résolue {} {} ", inv_even, rank_dist);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = inv_even - rank_dist  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return inv_even - rank_dist  + 100.0;

        }

        if CONJECTURE == 292 {

            // min_pos_eig <= n_sommer / meangravity

            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let mut min_pos_eig = f64::INFINITY;
            for e in 0..eig.eigenvalues.len(){
                if eig.eigenvalues[e] < min_pos_eig && eig.eigenvalues[e] > 0.00000001 {
                    min_pos_eig = eig.eigenvalues[e];
                }
            }

            let other = self.n_sommet as f64/invariants::gravity_matrix(&self.adj_mat).mean();

            if min_pos_eig - other > 0.0001{
                println!("conjecture 292 résolue {} {} ", min_pos_eig, other);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = min_pos_eig - other  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return min_pos_eig - other  + 100.0;

        }

        if CONJECTURE == 295 {

            // num_pos_eig <= n_sommer / meangravity

            let eig = SymmetricEigen::new(invariants::dist_matrix(&self.adj_mat));
            let mut num_pos_eig = 0.0;
            for e in 0..eig.eigenvalues.len(){
                if eig.eigenvalues[e] > 0.00000001 {
                    num_pos_eig += 1.0;
                }
            }

            let other = self.n_sommet as f64/invariants::gravity_matrix(&self.adj_mat).mean();

            if num_pos_eig - other > 0.0001{
                println!("conjecture 295 résolue {} {} ", num_pos_eig, other);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = num_pos_eig - other  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return num_pos_eig - other  + 100.0;

        }

        if CONJECTURE == 129 {

            // dev eigen laplacian <= randic index

            let eig = SymmetricEigen::new(invariants::laplacian_matrix(&self.adj_mat));
            let mut eig_vec = vec![];
            for e in 0..eig.eigenvalues.len(){
                eig_vec.push(eig.eigenvalues[e])
            }

            let dev_eig_lap = invariants::std_dev(eig_vec);

            let randic = invariants::randic_index(&self.adj_mat);

            if dev_eig_lap - randic > 0.0001{
                println!("conjecture 129 résolue {} {} ", dev_eig_lap, randic);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = dev_eig_lap - randic  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return dev_eig_lap - randic  + 100.0;

        }

        if CONJECTURE == 698 {

            // dev eigen laplacian <= randic index

            let eig = SymmetricEigen::new(invariants::laplacian_matrix(&self.adj_mat));
            let mut norme = 0.0;
            for e in 0..eig.eigenvalues.len(){
                if eig.eigenvalues[e] < -0.00000001 {
                    norme += eig.eigenvalues[e]*eig.eigenvalues[e];
                }
            }
            norme = norme.sqrt();

            let randic = invariants::randic_index(&self.adj_mat);

            if norme - randic > 0.0001{
                println!("conjecture 698 résolue {} {} ", norme, randic);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = norme - randic  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return norme - randic  + 100.0;

        }

        if CONJECTURE == 252 {

            // min deriv eigen laplacian <= sum 1/dual degree

            let eig = SymmetricEigen::new(invariants::laplacian_matrix(&self.adj_mat));
            let mut eig_vec = vec![];
            for e in 0..eig.eigenvalues.len(){
                eig_vec.push(eig.eigenvalues[e]);
            }
            let deriv = invariants::vec_derivative(eig_vec);
            let mut min_deriv = f64::INFINITY;
            for e in deriv{
                if e < min_deriv{
                    min_deriv = e;
                }
            }

            let mut sum = 0.0;
            for e in 0..self.n_sommet {
                sum += 1.0/invariants::dual_degree(&self.adj_mat, e);
            }


            if min_deriv - sum > 0.0001{
                println!("conjecture 252 résolue {} {} ", min_deriv, sum);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = min_deriv - sum  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return min_deriv - sum  + 100.0;

        }

        if CONJECTURE == 711 {

            // range deficience <= range eigen

            let eig = SymmetricEigen::new(self.adj_mat.clone());
            let range_eigen = eig.eigenvalues.max() - eig.eigenvalues.min();

            let mut min_def = f64::INFINITY;
            let mut max_def = f64::NEG_INFINITY;

            for i in 0..self.n_sommet{
                let def = invariants::deficience(&self.adj_mat, i);
                if def < min_def {
                    min_def = def;
                }
                if def > max_def {
                    max_def = def;
                }
            }

            let range_def = max_def-min_def;


            if range_def - range_eigen > 0.0001{
                println!("conjecture 711 résolue {} {} ", range_def, range_eigen);
                println!("{}", self.adj_mat);
                std::process::exit(123);
            }

            self.stored_score = range_def - range_eigen  + 100.0;;
            self.stored_score_pertinent = true;
            //println!("{}", self.stored_score);

            return range_def - range_eigen  + 100.0;

        }

        if CONJECTURE == 10000 {
                    //AIDA ABIAD, Extending a conjecture of Graham and Lovász on the distance characteristic polynomial, question 5.1
                    // Are the coefficients of the distance characteristic polynomial of any blockgraph with n vertices unimodal with peak between n/3 and n/2 rounded down

                    let eig = SymmetricEigen::new(invariants::dist_matrix(&self.adj_mat));

                    let charac_poly_c = invariants::charac_poly_coeffs(eig);

                    //println!("{:?}", charac_poly_c);


                    let mut unimodal = true;
                    let mut decroissant = true;
                    let mut peak = 0;
                    for i in 0..charac_poly_c.len()-1 {
                        if charac_poly_c[i] > charac_poly_c[i+1] {

                            if !decroissant { unimodal = false; }

                        }else{
                            if decroissant {
                                decroissant = false;
                                peak = i;
                            }

                        }
                    }

                    if self.n_sommet < 5 {
                        peak = 100;
                    }

                    if !unimodal {
                        println!("waaaaaa");
                    }

                    if peak < self.n_sommet/3 {
                        println!("conjecture Adia Abiad réfutée {} {} ", peak, self.n_sommet);
                        println!("{}", self.adj_mat);
                        println!("{:?}", charac_poly_c);
                        std::process::exit(123);

                    }

                    self.stored_score = 100.0 - (peak - self.n_sommet/3) as f64;
                    self.stored_score_pertinent = true;
                    //println!("{}", self.stored_score);

                    return 100.0 - (peak - self.n_sommet/3) as f64

                }


        return 0.0;
    }


    pub fn smoothedScore(&mut self) ->f64{return self.score();}

    pub fn heuristic(&mut self, m : Move) -> f64{
        let mut cl = self.clone();
        cl.play(m);
        return cl.score() - self.score(); }

    pub fn terminal(& self) -> bool{ return self.n_sommet>SIZE_TERMINAL; }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub struct Move{
    pub ind : i32,
    pub from : usize,
    pub to : i32
}

//réfutée ailleurs mais je ne trouve pas de contre exemple