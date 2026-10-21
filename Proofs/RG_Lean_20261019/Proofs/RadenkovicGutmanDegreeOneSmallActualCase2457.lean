/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2457 : Family 10 := level10.get ⟨1524,by decide⟩
def sourceMap2457 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2457 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2457_checked : acceptsGraphIso
    (source (graph core2457) (root 10) 0 0) DegreeOneSmallSpectrum1991.graph sourceMap2457=true := by decide +kernel
theorem fusedMap2457_checked : acceptsGraphIso
    (fused (graph core2457) (root 10) 0 0) DegreeOneSmallSpectrum1518.graph fusedMap2457=true := by decide +kernel
theorem certified2457 : Certified (graph core2457) (root 10) 0 0 :=
  of_native_maps core2457 DegreeOneSmallSpectrum1991.graph DegreeOneSmallSpectrum1518.graph
    sourceMap2457 fusedMap2457 sourceMap2457_checked fusedMap2457_checked
    DegreeOneSmallComparisons.comparison2457
#print axioms sourceMap2457_checked
#print axioms fusedMap2457_checked
#print axioms certified2457
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
