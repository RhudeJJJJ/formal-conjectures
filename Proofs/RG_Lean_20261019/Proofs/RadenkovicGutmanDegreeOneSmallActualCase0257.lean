/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0257 : Family 5 := level5.get ⟨13,by decide⟩
def sourceMap0257 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 5 0 2 v)
def fusedMap0257 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap0257_checked : acceptsGraphIso
    (source (graph core0257) (root 5) 0 2) DegreeOneSmallSpectrum093.graph sourceMap0257=true := by decide +kernel
theorem fusedMap0257_checked : acceptsGraphIso
    (fused (graph core0257) (root 5) 0 2) SmallGeFourSpectrum016.graph fusedMap0257=true := by decide +kernel
theorem certified0257 : Certified (graph core0257) (root 5) 0 2 :=
  of_native_maps core0257 DegreeOneSmallSpectrum093.graph SmallGeFourSpectrum016.graph
    sourceMap0257 fusedMap0257 sourceMap0257_checked fusedMap0257_checked
    DegreeOneSmallComparisons.comparison0257
#print axioms sourceMap0257_checked
#print axioms fusedMap0257_checked
#print axioms certified0257
def sourceMap0257swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,7,8,9,6] (sourceLabel 5 2 0 v)
def fusedMap0257swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap0257swap_checked : acceptsGraphIso
    (source (graph core0257) (root 5) 2 0) DegreeOneSmallSpectrum093.graph sourceMap0257swap=true := by decide +kernel
theorem fusedMap0257swap_checked : acceptsGraphIso
    (fused (graph core0257) (root 5) 2 0) SmallGeFourSpectrum016.graph fusedMap0257swap=true := by decide +kernel
theorem certified0257swap : Certified (graph core0257) (root 5) 2 0 :=
  of_native_maps core0257 DegreeOneSmallSpectrum093.graph SmallGeFourSpectrum016.graph
    sourceMap0257swap fusedMap0257swap sourceMap0257swap_checked fusedMap0257swap_checked
    DegreeOneSmallComparisons.comparison0257
#print axioms sourceMap0257swap_checked
#print axioms fusedMap0257swap_checked
#print axioms certified0257swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
