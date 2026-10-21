/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0191 : Family 5 := level5.get ⟨2,by decide⟩
def sourceMap0191 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,10,11,6,7,8,9] (sourceLabel 5 1 3 v)
def fusedMap0191 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 1 3 v)
theorem sourceMap0191_checked : acceptsGraphIso
    (source (graph core0191) (root 5) 1 3) DegreeOneSmallSpectrum559.graph sourceMap0191=true := by decide +kernel
theorem fusedMap0191_checked : acceptsGraphIso
    (fused (graph core0191) (root 5) 1 3) DegreeOneSmallSpectrum386.graph fusedMap0191=true := by decide +kernel
theorem certified0191 : Certified (graph core0191) (root 5) 1 3 :=
  of_native_maps core0191 DegreeOneSmallSpectrum559.graph DegreeOneSmallSpectrum386.graph
    sourceMap0191 fusedMap0191 sourceMap0191_checked fusedMap0191_checked
    DegreeOneSmallComparisons.comparison0191
#print axioms sourceMap0191_checked
#print axioms fusedMap0191_checked
#print axioms certified0191
def sourceMap0191swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 3 1 v)
def fusedMap0191swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 3 1 v)
theorem sourceMap0191swap_checked : acceptsGraphIso
    (source (graph core0191) (root 5) 3 1) DegreeOneSmallSpectrum559.graph sourceMap0191swap=true := by decide +kernel
theorem fusedMap0191swap_checked : acceptsGraphIso
    (fused (graph core0191) (root 5) 3 1) DegreeOneSmallSpectrum386.graph fusedMap0191swap=true := by decide +kernel
theorem certified0191swap : Certified (graph core0191) (root 5) 3 1 :=
  of_native_maps core0191 DegreeOneSmallSpectrum559.graph DegreeOneSmallSpectrum386.graph
    sourceMap0191swap fusedMap0191swap sourceMap0191swap_checked fusedMap0191swap_checked
    DegreeOneSmallComparisons.comparison0191
#print axioms sourceMap0191swap_checked
#print axioms fusedMap0191swap_checked
#print axioms certified0191swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
