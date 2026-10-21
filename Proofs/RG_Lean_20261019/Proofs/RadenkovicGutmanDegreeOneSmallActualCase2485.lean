/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2485 : Family 10 := level10.get ⟨1800,by decide⟩
def sourceMap2485 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2485 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2485_checked : acceptsGraphIso
    (source (graph core2485) (root 10) 0 0) DegreeOneSmallSpectrum1987.graph sourceMap2485=true := by decide +kernel
theorem fusedMap2485_checked : acceptsGraphIso
    (fused (graph core2485) (root 10) 0 0) DegreeOneSmallSpectrum1988.graph fusedMap2485=true := by decide +kernel
theorem certified2485 : Certified (graph core2485) (root 10) 0 0 :=
  of_native_maps core2485 DegreeOneSmallSpectrum1987.graph DegreeOneSmallSpectrum1988.graph
    sourceMap2485 fusedMap2485 sourceMap2485_checked fusedMap2485_checked
    DegreeOneSmallComparisons.comparison2485
#print axioms sourceMap2485_checked
#print axioms fusedMap2485_checked
#print axioms certified2485
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
