/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0589 : Family 10 := level10.get ⟨664,by decide⟩
def sourceMap0589 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,11,12,7,8,9,10] (sourceLabel 10 0 0 v)
def fusedMap0589 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,11,12,7,8,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0589_checked : acceptsGraphIso
    (source (graph core0589) (root 10) 0 0) DegreeOneSmallSpectrum1261.graph sourceMap0589=true := by decide +kernel
theorem fusedMap0589_checked : acceptsGraphIso
    (fused (graph core0589) (root 10) 0 0) DegreeOneSmallSpectrum1254.graph fusedMap0589=true := by decide +kernel
theorem certified0589 : Certified (graph core0589) (root 10) 0 0 :=
  of_native_maps core0589 DegreeOneSmallSpectrum1261.graph DegreeOneSmallSpectrum1254.graph
    sourceMap0589 fusedMap0589 sourceMap0589_checked fusedMap0589_checked
    DegreeTwoThreeFiniteComparisons.comparison0589
#print axioms sourceMap0589_checked
#print axioms fusedMap0589_checked
#print axioms certified0589
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
