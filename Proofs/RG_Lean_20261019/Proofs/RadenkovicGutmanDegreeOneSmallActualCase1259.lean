/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1259 : Family 9 := level9.get ⟨38,by decide⟩
def sourceMap1259 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,8,9,10,11,6,7,4,5] (sourceLabel 9 0 0 v)
def fusedMap1259 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1259_checked : acceptsGraphIso
    (source (graph core1259) (root 9) 0 0) DegreeOneSmallSpectrum434.graph sourceMap1259=true := by decide +kernel
theorem fusedMap1259_checked : acceptsGraphIso
    (fused (graph core1259) (root 9) 0 0) DegreeOneSmallSpectrum387.graph fusedMap1259=true := by decide +kernel
theorem certified1259 : Certified (graph core1259) (root 9) 0 0 :=
  of_native_maps core1259 DegreeOneSmallSpectrum434.graph DegreeOneSmallSpectrum387.graph
    sourceMap1259 fusedMap1259 sourceMap1259_checked fusedMap1259_checked
    DegreeOneSmallComparisons.comparison1259
#print axioms sourceMap1259_checked
#print axioms fusedMap1259_checked
#print axioms certified1259
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
