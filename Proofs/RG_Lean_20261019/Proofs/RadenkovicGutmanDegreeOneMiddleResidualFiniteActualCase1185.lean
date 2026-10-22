/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1185 : Family 10 := level10.get ⟨1566,by decide⟩
def sourceMap1185 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1185 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1185_checked : acceptsGraphIso
    (source (graph core1185) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2341.graph sourceMap1185=true := by decide +kernel
theorem fusedMap1185_checked : acceptsGraphIso
    (fused (graph core1185) (root 10) 2 2) DegreeTwoThreeSpectrum6045.graph fusedMap1185=true := by decide +kernel
theorem certified1185 : Certified (graph core1185) (root 10) 2 2 :=
  of_native_maps core1185 DegreeOneMiddleResidualSpectrum2341.graph DegreeTwoThreeSpectrum6045.graph
    sourceMap1185 fusedMap1185 sourceMap1185_checked fusedMap1185_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1185
#print axioms sourceMap1185_checked
#print axioms fusedMap1185_checked
#print axioms certified1185
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
