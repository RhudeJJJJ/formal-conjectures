/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2331 : Family 10 := level10.get ⟨1036,by decide⟩
def sourceMap2331 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2331 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2331_checked : acceptsGraphIso
    (source (graph core2331) (root 10) 0 0) DegreeOneSmallSpectrum1618.graph sourceMap2331=true := by decide +kernel
theorem fusedMap2331_checked : acceptsGraphIso
    (fused (graph core2331) (root 10) 0 0) DegreeOneSmallSpectrum1620.graph fusedMap2331=true := by decide +kernel
theorem certified2331 : Certified (graph core2331) (root 10) 0 0 :=
  of_native_maps core2331 DegreeOneSmallSpectrum1618.graph DegreeOneSmallSpectrum1620.graph
    sourceMap2331 fusedMap2331 sourceMap2331_checked fusedMap2331_checked
    DegreeOneSmallComparisons.comparison2331
#print axioms sourceMap2331_checked
#print axioms fusedMap2331_checked
#print axioms certified2331
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
