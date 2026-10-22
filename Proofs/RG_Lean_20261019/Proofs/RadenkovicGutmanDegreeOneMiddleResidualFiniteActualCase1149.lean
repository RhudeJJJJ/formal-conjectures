/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1149 : Family 10 := level10.get ⟨1347,by decide⟩
def sourceMap1149 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1149 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1149_checked : acceptsGraphIso
    (source (graph core1149) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2222.graph sourceMap1149=true := by decide +kernel
theorem fusedMap1149_checked : acceptsGraphIso
    (fused (graph core1149) (root 10) 2 2) DegreeTwoThreeSpectrum6678.graph fusedMap1149=true := by decide +kernel
theorem certified1149 : Certified (graph core1149) (root 10) 2 2 :=
  of_native_maps core1149 DegreeOneMiddleResidualSpectrum2222.graph DegreeTwoThreeSpectrum6678.graph
    sourceMap1149 fusedMap1149 sourceMap1149_checked fusedMap1149_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1149
#print axioms sourceMap1149_checked
#print axioms fusedMap1149_checked
#print axioms certified1149
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
