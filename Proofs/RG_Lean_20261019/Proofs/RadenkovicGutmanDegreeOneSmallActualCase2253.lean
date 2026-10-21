/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2253 : Family 10 := level10.get ⟨830,by decide⟩
def sourceMap2253 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2253 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2253_checked : acceptsGraphIso
    (source (graph core2253) (root 10) 0 0) DegreeOneSmallSpectrum1876.graph sourceMap2253=true := by decide +kernel
theorem fusedMap2253_checked : acceptsGraphIso
    (fused (graph core2253) (root 10) 0 0) DegreeOneSmallSpectrum1456.graph fusedMap2253=true := by decide +kernel
theorem certified2253 : Certified (graph core2253) (root 10) 0 0 :=
  of_native_maps core2253 DegreeOneSmallSpectrum1876.graph DegreeOneSmallSpectrum1456.graph
    sourceMap2253 fusedMap2253 sourceMap2253_checked fusedMap2253_checked
    DegreeOneSmallComparisons.comparison2253
#print axioms sourceMap2253_checked
#print axioms fusedMap2253_checked
#print axioms certified2253
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
