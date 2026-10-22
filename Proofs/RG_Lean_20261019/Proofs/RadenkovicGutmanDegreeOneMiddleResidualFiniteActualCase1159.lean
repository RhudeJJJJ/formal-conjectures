/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1159 : Family 10 := level10.get ⟨1406,by decide⟩
def sourceMap1159 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1159 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1159_checked : acceptsGraphIso
    (source (graph core1159) (root 10) 2 2) DegreeTwoThreeSpectrum7491.graph sourceMap1159=true := by decide +kernel
theorem fusedMap1159_checked : acceptsGraphIso
    (fused (graph core1159) (root 10) 2 2) DegreeTwoThreeSpectrum6803.graph fusedMap1159=true := by decide +kernel
theorem certified1159 : Certified (graph core1159) (root 10) 2 2 :=
  of_native_maps core1159 DegreeTwoThreeSpectrum7491.graph DegreeTwoThreeSpectrum6803.graph
    sourceMap1159 fusedMap1159 sourceMap1159_checked fusedMap1159_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1159
#print axioms sourceMap1159_checked
#print axioms fusedMap1159_checked
#print axioms certified1159
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
