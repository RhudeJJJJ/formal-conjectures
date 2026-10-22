/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4501 : Family 10 := level10.get ⟨289,by decide⟩
def sourceMap4501 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4501 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4501_checked : acceptsGraphIso
    (source (graph core4501) (root 10) 2 2) DegreeTwoThreeSpectrum6524.graph sourceMap4501=true := by decide +kernel
theorem fusedMap4501_checked : acceptsGraphIso
    (fused (graph core4501) (root 10) 2 2) DegreeTwoThreeSpectrum5440.graph fusedMap4501=true := by decide +kernel
theorem certified4501 : Certified (graph core4501) (root 10) 2 2 :=
  of_native_maps core4501 DegreeTwoThreeSpectrum6524.graph DegreeTwoThreeSpectrum5440.graph
    sourceMap4501 fusedMap4501 sourceMap4501_checked fusedMap4501_checked
    DegreeTwoThreeFiniteComparisons.comparison4501
#print axioms sourceMap4501_checked
#print axioms fusedMap4501_checked
#print axioms certified4501
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
