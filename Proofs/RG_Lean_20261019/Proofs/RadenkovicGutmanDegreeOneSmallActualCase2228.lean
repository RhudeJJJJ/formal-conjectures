/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2228 : Family 10 := level10.get ⟨767,by decide⟩
def sourceMap2228 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2228 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2228_checked : acceptsGraphIso
    (source (graph core2228) (root 10) 0 0) DegreeOneSmallSpectrum1871.graph sourceMap2228=true := by decide +kernel
theorem fusedMap2228_checked : acceptsGraphIso
    (fused (graph core2228) (root 10) 0 0) DegreeOneSmallSpectrum1399.graph fusedMap2228=true := by decide +kernel
theorem certified2228 : Certified (graph core2228) (root 10) 0 0 :=
  of_native_maps core2228 DegreeOneSmallSpectrum1871.graph DegreeOneSmallSpectrum1399.graph
    sourceMap2228 fusedMap2228 sourceMap2228_checked fusedMap2228_checked
    DegreeOneSmallComparisons.comparison2228
#print axioms sourceMap2228_checked
#print axioms fusedMap2228_checked
#print axioms certified2228
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
