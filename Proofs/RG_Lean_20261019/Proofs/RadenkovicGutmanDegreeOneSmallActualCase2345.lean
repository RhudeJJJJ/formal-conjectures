/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2345 : Family 10 := level10.get ⟨1066,by decide⟩
def sourceMap2345 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2345 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2345_checked : acceptsGraphIso
    (source (graph core2345) (root 10) 0 0) DegreeOneSmallSpectrum1688.graph sourceMap2345=true := by decide +kernel
theorem fusedMap2345_checked : acceptsGraphIso
    (fused (graph core2345) (root 10) 0 0) DegreeOneSmallSpectrum1687.graph fusedMap2345=true := by decide +kernel
theorem certified2345 : Certified (graph core2345) (root 10) 0 0 :=
  of_native_maps core2345 DegreeOneSmallSpectrum1688.graph DegreeOneSmallSpectrum1687.graph
    sourceMap2345 fusedMap2345 sourceMap2345_checked fusedMap2345_checked
    DegreeOneSmallComparisons.comparison2345
#print axioms sourceMap2345_checked
#print axioms fusedMap2345_checked
#print axioms certified2345
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
