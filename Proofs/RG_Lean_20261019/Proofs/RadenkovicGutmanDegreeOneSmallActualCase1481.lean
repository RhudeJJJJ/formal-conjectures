/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1481 : Family 9 := level9.get ⟨215,by decide⟩
def sourceMap1481 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1481 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1481_checked : acceptsGraphIso
    (source (graph core1481) (root 9) 0 0) SmallGeFourSpectrum153.graph sourceMap1481=true := by decide +kernel
theorem fusedMap1481_checked : acceptsGraphIso
    (fused (graph core1481) (root 9) 0 0) SmallGeFourSpectrum103.graph fusedMap1481=true := by decide +kernel
theorem certified1481 : Certified (graph core1481) (root 9) 0 0 :=
  of_native_maps core1481 SmallGeFourSpectrum153.graph SmallGeFourSpectrum103.graph
    sourceMap1481 fusedMap1481 sourceMap1481_checked fusedMap1481_checked
    DegreeOneSmallComparisons.comparison1481
#print axioms sourceMap1481_checked
#print axioms fusedMap1481_checked
#print axioms certified1481
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
