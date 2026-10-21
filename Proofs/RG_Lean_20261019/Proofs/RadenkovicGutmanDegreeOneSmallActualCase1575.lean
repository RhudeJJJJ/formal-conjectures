/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1575 : Family 9 := level9.get ⟨319,by decide⟩
def sourceMap1575 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1575 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1575_checked : acceptsGraphIso
    (source (graph core1575) (root 9) 0 0) SmallGeFourSpectrum123.graph sourceMap1575=true := by decide +kernel
theorem fusedMap1575_checked : acceptsGraphIso
    (fused (graph core1575) (root 9) 0 0) SmallGeFourSpectrum128.graph fusedMap1575=true := by decide +kernel
theorem certified1575 : Certified (graph core1575) (root 9) 0 0 :=
  of_native_maps core1575 SmallGeFourSpectrum123.graph SmallGeFourSpectrum128.graph
    sourceMap1575 fusedMap1575 sourceMap1575_checked fusedMap1575_checked
    DegreeOneSmallComparisons.comparison1575
#print axioms sourceMap1575_checked
#print axioms fusedMap1575_checked
#print axioms certified1575
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
