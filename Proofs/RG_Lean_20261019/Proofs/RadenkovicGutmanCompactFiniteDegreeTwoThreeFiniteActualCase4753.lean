/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4753 : Family 10 := level10.get ⟨1011,by decide⟩
def sourceMap4753 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4753 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4753_checked : acceptsGraphIso
    (source (graph core4753) (root 10) 2 2) DegreeTwoThreeSpectrum7087.graph sourceMap4753=true := by decide +kernel
theorem fusedMap4753_checked : acceptsGraphIso
    (fused (graph core4753) (root 10) 2 2) DegreeTwoThreeSpectrum6003.graph fusedMap4753=true := by decide +kernel
theorem certified4753 : Certified (graph core4753) (root 10) 2 2 :=
  of_native_maps core4753 DegreeTwoThreeSpectrum7087.graph DegreeTwoThreeSpectrum6003.graph
    sourceMap4753 fusedMap4753 sourceMap4753_checked fusedMap4753_checked
    DegreeTwoThreeFiniteComparisons.comparison4753
#print axioms sourceMap4753_checked
#print axioms fusedMap4753_checked
#print axioms certified4753
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
