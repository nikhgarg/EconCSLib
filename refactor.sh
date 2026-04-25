#!/bin/bash
set -e

# 1. Create the target directories
mkdir -p EconCSLean/Foundations/Math
mkdir -p EconCSLean/Foundations/Probability
mkdir -p EconCSLean/Foundations/Optimization
mkdir -p EconCSLean/Foundations/Graph
mkdir -p EconCSLean/Foundations/Econometrics/RatingModels

mkdir -p EconCSLean/MechanismDesign/Auctions
mkdir -p EconCSLean/SocialChoice/FairDivision
mkdir -p EconCSLean/Markets/Matching

mkdir -p EconCSLean/Learning/Bandits
mkdir -p EconCSLean/Learning/LearningInGames
mkdir -p EconCSLean/Algorithms/Online
mkdir -p EconCSLean/Algorithms/Complexity

mkdir -p EconCSLean/Applications/RecommenderSystems
mkdir -p papers

# 2. Move Core files to their new semantic locations
# MechanismDesign/Auctions
[ -d EconCSLean/Auction ] && mv EconCSLean/Auction/* EconCSLean/MechanismDesign/Auctions/
[ -f EconCSLean/Auction.lean ] && mv EconCSLean/Auction.lean EconCSLean/MechanismDesign/Auctions.lean

# SocialChoice/FairDivision
[ -d EconCSLean/FairDivision ] && mv EconCSLean/FairDivision/* EconCSLean/SocialChoice/FairDivision/
[ -f EconCSLean/FairDivision.lean ] && mv EconCSLean/FairDivision.lean EconCSLean/SocialChoice/FairDivision.lean

# Markets/Matching
[ -d EconCSLean/Matching ] && mv EconCSLean/Matching/* EconCSLean/Markets/Matching/
[ -f EconCSLean/Matching.lean ] && mv EconCSLean/Matching.lean EconCSLean/Markets/Matching.lean

# Foundations/Graph
[ -d EconCSLean/Graph ] && mv EconCSLean/Graph/* EconCSLean/Foundations/Graph/
[ -f EconCSLean/Graph.lean ] && mv EconCSLean/Graph.lean EconCSLean/Foundations/Graph.lean

# Foundations/Math
[ -d EconCSLean/Math ] && mv EconCSLean/Math/* EconCSLean/Foundations/Math/
[ -f EconCSLean/Math.lean ] && mv EconCSLean/Math.lean EconCSLean/Foundations/Math.lean

# Algorithms/Online
[ -d EconCSLean/Online ] && mv EconCSLean/Online/* EconCSLean/Algorithms/Online/
[ -f EconCSLean/Online.lean ] && mv EconCSLean/Online.lean EconCSLean/Algorithms/Online.lean

# Split Decision
if [ -d EconCSLean/Decision ]; then
  [ -f EconCSLean/Decision/Argmax.lean ] && mv EconCSLean/Decision/Argmax.lean EconCSLean/Foundations/Optimization/
  [ -f EconCSLean/Decision/ThompsonSampling.lean ] && mv EconCSLean/Decision/ThompsonSampling.lean EconCSLean/Learning/Bandits/
  [ -f EconCSLean/Decision/Yao.lean ] && mv EconCSLean/Decision/Yao.lean EconCSLean/Algorithms/Complexity/
fi
[ -f EconCSLean/Decision.lean ] && rm EconCSLean/Decision.lean # Umbrella no longer makes sense

# Split Statistics
if [ -d EconCSLean/Statistics ]; then
  [ -f EconCSLean/Statistics/FinsetVariance.lean ] && mv EconCSLean/Statistics/FinsetVariance.lean EconCSLean/Foundations/Probability/
  [ -f EconCSLean/Statistics/BinaryRating.lean ] && mv EconCSLean/Statistics/BinaryRating.lean EconCSLean/Foundations/Econometrics/RatingModels/
  [ -f EconCSLean/Statistics/OrdinalRating.lean ] && mv EconCSLean/Statistics/OrdinalRating.lean EconCSLean/Foundations/Econometrics/RatingModels/
fi
[ -f EconCSLean/Statistics.lean ] && rm EconCSLean/Statistics.lean

# Split DecisionCore
if [ -d DecisionCore ]; then
  mv DecisionCore/FiniteExpectation.lean EconCSLean/Foundations/Probability/
  mv DecisionCore/Conditional.lean EconCSLean/Foundations/Probability/
  mv DecisionCore/EpsilonContinuity.lean EconCSLean/Foundations/Math/
  mv DecisionCore/IntervalCrossing.lean EconCSLean/Foundations/Math/
  mv DecisionCore/FiniteSigns.lean EconCSLean/Foundations/Math/

  mv DecisionCore/Policy.lean EconCSLean/Applications/RecommenderSystems/
  mv DecisionCore/PolicyAveraging.lean EconCSLean/Applications/RecommenderSystems/
  mv DecisionCore/Allocation.lean EconCSLean/Applications/RecommenderSystems/
  mv DecisionCore/Classwise.lean EconCSLean/Applications/RecommenderSystems/
fi
[ -f DecisionCore.lean ] && rm DecisionCore.lean
[ -f DecisionFairness.lean ] && mv DecisionFairness.lean EconCSLean/Applications/RecommenderSystems/

# Clean empty dirs
rm -rf EconCSLean/Auction EconCSLean/FairDivision EconCSLean/Matching EconCSLean/Graph EconCSLean/Math EconCSLean/Online EconCSLean/Decision EconCSLean/Statistics DecisionCore

# 3. Move papers to papers/
for paper in Monoculture AccuracyDiversity UserItemFairness ProducerFairness DiscretizationBias; do
  if [ -d "$paper" ]; then
    mv "$paper" "papers/"
  fi
  if [ -f "${paper}.lean" ]; then
    mv "${paper}.lean" "papers/"
  fi
done

# 4. Rewrite imports in all .lean files
find . -name "*.lean" -type f -exec sed -i \
  -e 's/EconCSLean\.Auction/EconCSLean.MechanismDesign.Auctions/g' \
  -e 's/EconCSLean\.FairDivision/EconCSLean.SocialChoice.FairDivision/g' \
  -e 's/EconCSLean\.Matching/EconCSLean.Markets.Matching/g' \
  -e 's/EconCSLean\.Graph/EconCSLean.Foundations.Graph/g' \
  -e 's/EconCSLean\.Math/EconCSLean.Foundations.Math/g' \
  -e 's/EconCSLean\.Online/EconCSLean.Algorithms.Online/g' \
  -e 's/EconCSLean\.Decision\.Argmax/EconCSLean.Foundations.Optimization.Argmax/g' \
  -e 's/EconCSLean\.Decision\.ThompsonSampling/EconCSLean.Learning.Bandits.ThompsonSampling/g' \
  -e 's/EconCSLean\.Decision\.Yao/EconCSLean.Algorithms.Complexity.Yao/g' \
  -e 's/EconCSLean\.Statistics\.FinsetVariance/EconCSLean.Foundations.Probability.FinsetVariance/g' \
  -e 's/EconCSLean\.Statistics\.BinaryRating/EconCSLean.Foundations.Econometrics.RatingModels.BinaryRating/g' \
  -e 's/EconCSLean\.Statistics\.OrdinalRating/EconCSLean.Foundations.Econometrics.RatingModels.OrdinalRating/g' \
  -e 's/DecisionCore\.FiniteExpectation/EconCSLean.Foundations.Probability.FiniteExpectation/g' \
  -e 's/DecisionCore\.Conditional/EconCSLean.Foundations.Probability.Conditional/g' \
  -e 's/DecisionCore\.EpsilonContinuity/EconCSLean.Foundations.Math.EpsilonContinuity/g' \
  -e 's/DecisionCore\.IntervalCrossing/EconCSLean.Foundations.Math.IntervalCrossing/g' \
  -e 's/DecisionCore\.FiniteSigns/EconCSLean.Foundations.Math.FiniteSigns/g' \
  -e 's/DecisionCore\.PolicyAveraging/EconCSLean.Applications.RecommenderSystems.PolicyAveraging/g' \
  -e 's/DecisionCore\.Policy/EconCSLean.Applications.RecommenderSystems.Policy/g' \
  -e 's/DecisionCore\.Allocation/EconCSLean.Applications.RecommenderSystems.Allocation/g' \
  -e 's/DecisionCore\.Classwise/EconCSLean.Applications.RecommenderSystems.Classwise/g' \
  -e 's/import DecisionFairness/import EconCSLean.Applications.RecommenderSystems.DecisionFairness/g' \
  -e 's/namespace DecisionCore/namespace EconCSLean/g' \
  {} +

# 5. Fix root EconCSLean.lean umbrella file
cat << 'UMBRELLA' > EconCSLean.lean
import EconCSLean.Foundations.Graph
import EconCSLean.Foundations.Math
import EconCSLean.MechanismDesign.Auctions
import EconCSLean.SocialChoice.FairDivision
import EconCSLean.Markets.Matching
import EconCSLean.Algorithms.Online
UMBRELLA

# 6. Update lakefile.toml to point papers to papers/ srcDir
cat << 'LAKE' > lakefile.toml
name = "EconCSLean"
version = "0.1.0"
keywords = ["math"]
defaultTargets = ["EconCSLean"]

[leanOptions]
pp.unicode.fun = true # pretty-prints `fun a ↦ b`
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3
weak.linter.unnecessarySimpa = false
weak.linter.unusedDecidableInType = false
weak.linter.unusedFintypeInType = false
weak.linter.unusedSectionVars = false
weak.linter.unusedVariables = false
weak.linter.flexible = false
weak.linter.style.longLine = false
weak.linter.style.whitespace = false

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.30.0-rc2"

[[require]]
name = "cslib"
scope = "leanprover"
rev = "v4.30.0-rc2"

[[lean_lib]]
name = "EconCSLean"

[[lean_lib]]
name = "Monoculture"
srcDir = "papers"

[[lean_lib]]
name = "UserItemFairness"
srcDir = "papers"

[[lean_lib]]
name = "AccuracyDiversity"
srcDir = "papers"

[[lean_lib]]
name = "DiscretizationBias"
srcDir = "papers"

[[lean_lib]]
name = "ProducerFairness"
srcDir = "papers"
LAKE

