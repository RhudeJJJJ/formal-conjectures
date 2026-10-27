/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4755 : Family 10 := level10.get ⟨1017,by decide⟩
def sourceMap4755 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4755 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4755_checked : acceptsGraphIso
    (source (graph core4755) (root 10) 2 2) DegreeTwoThreeSpectrum7093.graph sourceMap4755=true := by decide +kernel
theorem fusedMap4755_checked : acceptsGraphIso
    (fused (graph core4755) (root 10) 2 2) DegreeTwoThreeSpectrum6016.graph fusedMap4755=true := by decide +kernel
theorem certified4755 : Certified (graph core4755) (root 10) 2 2 :=
  of_native_maps core4755 DegreeTwoThreeSpectrum7093.graph DegreeTwoThreeSpectrum6016.graph
    sourceMap4755 fusedMap4755 sourceMap4755_checked fusedMap4755_checked
    DegreeTwoThreeFiniteComparisons.comparison4755
#print axioms sourceMap4755_checked
#print axioms fusedMap4755_checked
#print axioms certified4755
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
