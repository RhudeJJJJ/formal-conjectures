/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2473 : Family 10 := level10.get ⟨1583,by decide⟩
def sourceMap2473 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (sourceLabel 10 0 0 v)
def fusedMap2473 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2473_checked : acceptsGraphIso
    (source (graph core2473) (root 10) 0 0) DegreeOneSmallSpectrum2008.graph sourceMap2473=true := by decide +kernel
theorem fusedMap2473_checked : acceptsGraphIso
    (fused (graph core2473) (root 10) 0 0) DegreeOneSmallSpectrum1638.graph fusedMap2473=true := by decide +kernel
theorem certified2473 : Certified (graph core2473) (root 10) 0 0 :=
  of_native_maps core2473 DegreeOneSmallSpectrum2008.graph DegreeOneSmallSpectrum1638.graph
    sourceMap2473 fusedMap2473 sourceMap2473_checked fusedMap2473_checked
    DegreeOneSmallComparisons.comparison2473
#print axioms sourceMap2473_checked
#print axioms fusedMap2473_checked
#print axioms certified2473
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
