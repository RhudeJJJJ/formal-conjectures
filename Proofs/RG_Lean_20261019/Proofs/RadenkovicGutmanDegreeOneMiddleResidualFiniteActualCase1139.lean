/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1139 : Family 10 := level10.get ⟨1307,by decide⟩
def sourceMap1139 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1139 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1139_checked : acceptsGraphIso
    (source (graph core1139) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2194.graph sourceMap1139=true := by decide +kernel
theorem fusedMap1139_checked : acceptsGraphIso
    (fused (graph core1139) (root 10) 2 2) DegreeTwoThreeSpectrum6603.graph fusedMap1139=true := by decide +kernel
theorem certified1139 : Certified (graph core1139) (root 10) 2 2 :=
  of_native_maps core1139 DegreeOneMiddleResidualSpectrum2194.graph DegreeTwoThreeSpectrum6603.graph
    sourceMap1139 fusedMap1139 sourceMap1139_checked fusedMap1139_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1139
#print axioms sourceMap1139_checked
#print axioms fusedMap1139_checked
#print axioms certified1139
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
