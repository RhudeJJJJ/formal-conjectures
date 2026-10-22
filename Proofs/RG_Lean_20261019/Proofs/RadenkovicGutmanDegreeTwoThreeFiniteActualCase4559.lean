/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4559 : Family 10 := level10.get ⟨477,by decide⟩
def sourceMap4559 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,9,10,11,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4559 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4559_checked : acceptsGraphIso
    (source (graph core4559) (root 10) 2 2) DegreeTwoThreeSpectrum6821.graph sourceMap4559=true := by decide +kernel
theorem fusedMap4559_checked : acceptsGraphIso
    (fused (graph core4559) (root 10) 2 2) DegreeTwoThreeSpectrum5940.graph fusedMap4559=true := by decide +kernel
theorem certified4559 : Certified (graph core4559) (root 10) 2 2 :=
  of_native_maps core4559 DegreeTwoThreeSpectrum6821.graph DegreeTwoThreeSpectrum5940.graph
    sourceMap4559 fusedMap4559 sourceMap4559_checked fusedMap4559_checked
    DegreeTwoThreeFiniteComparisons.comparison4559
#print axioms sourceMap4559_checked
#print axioms fusedMap4559_checked
#print axioms certified4559
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
