/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0969 : Family 8 := level8.get ⟨83,by decide⟩
def sourceMap0969 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap0969 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0969_checked : acceptsGraphIso
    (source (graph core0969) (root 8) 0 2) DegreeOneSmallSpectrum1504.graph sourceMap0969=true := by decide +kernel
theorem fusedMap0969_checked : acceptsGraphIso
    (fused (graph core0969) (root 8) 0 2) DegreeOneSmallSpectrum967.graph fusedMap0969=true := by decide +kernel
theorem certified0969 : Certified (graph core0969) (root 8) 0 2 :=
  of_native_maps core0969 DegreeOneSmallSpectrum1504.graph DegreeOneSmallSpectrum967.graph
    sourceMap0969 fusedMap0969 sourceMap0969_checked fusedMap0969_checked
    DegreeOneSmallComparisons.comparison0969
#print axioms sourceMap0969_checked
#print axioms fusedMap0969_checked
#print axioms certified0969
def sourceMap0969swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 2 0 v)
def fusedMap0969swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0969swap_checked : acceptsGraphIso
    (source (graph core0969) (root 8) 2 0) DegreeOneSmallSpectrum1504.graph sourceMap0969swap=true := by decide +kernel
theorem fusedMap0969swap_checked : acceptsGraphIso
    (fused (graph core0969) (root 8) 2 0) DegreeOneSmallSpectrum967.graph fusedMap0969swap=true := by decide +kernel
theorem certified0969swap : Certified (graph core0969) (root 8) 2 0 :=
  of_native_maps core0969 DegreeOneSmallSpectrum1504.graph DegreeOneSmallSpectrum967.graph
    sourceMap0969swap fusedMap0969swap sourceMap0969swap_checked fusedMap0969swap_checked
    DegreeOneSmallComparisons.comparison0969
#print axioms sourceMap0969swap_checked
#print axioms fusedMap0969swap_checked
#print axioms certified0969swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
