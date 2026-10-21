/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0978 : Family 8 := level8.get ⟨85,by decide⟩
def sourceMap0978 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,6,7,8,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0978 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0978_checked : acceptsGraphIso
    (source (graph core0978) (root 8) 1 1) DegreeOneSmallSpectrum1316.graph sourceMap0978=true := by decide +kernel
theorem fusedMap0978_checked : acceptsGraphIso
    (fused (graph core0978) (root 8) 1 1) DegreeOneSmallSpectrum969.graph fusedMap0978=true := by decide +kernel
theorem certified0978 : Certified (graph core0978) (root 8) 1 1 :=
  of_native_maps core0978 DegreeOneSmallSpectrum1316.graph DegreeOneSmallSpectrum969.graph
    sourceMap0978 fusedMap0978 sourceMap0978_checked fusedMap0978_checked
    DegreeOneSmallComparisons.comparison0978
#print axioms sourceMap0978_checked
#print axioms fusedMap0978_checked
#print axioms certified0978
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
