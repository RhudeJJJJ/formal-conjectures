/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2282 : Family 10 := level10.get ⟨885,by decide⟩
def sourceMap2282 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2282 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2282_checked : acceptsGraphIso
    (source (graph core2282) (root 10) 0 0) DegreeOneSmallSpectrum1754.graph sourceMap2282=true := by decide +kernel
theorem fusedMap2282_checked : acceptsGraphIso
    (fused (graph core2282) (root 10) 0 0) DegreeOneSmallSpectrum1483.graph fusedMap2282=true := by decide +kernel
theorem certified2282 : Certified (graph core2282) (root 10) 0 0 :=
  of_native_maps core2282 DegreeOneSmallSpectrum1754.graph DegreeOneSmallSpectrum1483.graph
    sourceMap2282 fusedMap2282 sourceMap2282_checked fusedMap2282_checked
    DegreeOneSmallComparisons.comparison2282
#print axioms sourceMap2282_checked
#print axioms fusedMap2282_checked
#print axioms certified2282
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
