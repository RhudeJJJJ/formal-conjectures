/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4551 : Family 10 := level10.get ⟨453,by decide⟩
def sourceMap4551 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4551 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4551_checked : acceptsGraphIso
    (source (graph core4551) (root 10) 2 2) DegreeTwoThreeSpectrum6814.graph sourceMap4551=true := by decide +kernel
theorem fusedMap4551_checked : acceptsGraphIso
    (fused (graph core4551) (root 10) 2 2) DegreeTwoThreeSpectrum5883.graph fusedMap4551=true := by decide +kernel
theorem certified4551 : Certified (graph core4551) (root 10) 2 2 :=
  of_native_maps core4551 DegreeTwoThreeSpectrum6814.graph DegreeTwoThreeSpectrum5883.graph
    sourceMap4551 fusedMap4551 sourceMap4551_checked fusedMap4551_checked
    DegreeTwoThreeFiniteComparisons.comparison4551
#print axioms sourceMap4551_checked
#print axioms fusedMap4551_checked
#print axioms certified4551
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
