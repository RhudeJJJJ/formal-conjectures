/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4890 : Family 10 := level10.get ⟨1349,by decide⟩
def sourceMap4890 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4890 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4890_checked : acceptsGraphIso
    (source (graph core4890) (root 10) 2 2) DegreeTwoThreeSpectrum7433.graph sourceMap4890=true := by decide +kernel
theorem fusedMap4890_checked : acceptsGraphIso
    (fused (graph core4890) (root 10) 2 2) DegreeTwoThreeSpectrum6680.graph fusedMap4890=true := by decide +kernel
theorem certified4890 : Certified (graph core4890) (root 10) 2 2 :=
  of_native_maps core4890 DegreeTwoThreeSpectrum7433.graph DegreeTwoThreeSpectrum6680.graph
    sourceMap4890 fusedMap4890 sourceMap4890_checked fusedMap4890_checked
    DegreeTwoThreeFiniteComparisons.comparison4890
#print axioms sourceMap4890_checked
#print axioms fusedMap4890_checked
#print axioms certified4890
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
