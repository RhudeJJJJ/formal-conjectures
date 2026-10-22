/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1119 : Family 10 := level10.get ⟨1250,by decide⟩
def sourceMap1119 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1119 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1119_checked : acceptsGraphIso
    (source (graph core1119) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2151.graph sourceMap1119=true := by decide +kernel
theorem fusedMap1119_checked : acceptsGraphIso
    (fused (graph core1119) (root 10) 2 2) DegreeTwoThreeSpectrum6489.graph fusedMap1119=true := by decide +kernel
theorem certified1119 : Certified (graph core1119) (root 10) 2 2 :=
  of_native_maps core1119 DegreeOneMiddleResidualSpectrum2151.graph DegreeTwoThreeSpectrum6489.graph
    sourceMap1119 fusedMap1119 sourceMap1119_checked fusedMap1119_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1119
#print axioms sourceMap1119_checked
#print axioms fusedMap1119_checked
#print axioms certified1119
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
