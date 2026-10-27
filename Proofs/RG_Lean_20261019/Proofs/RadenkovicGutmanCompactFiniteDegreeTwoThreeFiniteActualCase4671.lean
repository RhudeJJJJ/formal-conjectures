/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4671 : Family 10 := level10.get ⟨804,by decide⟩
def sourceMap4671 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,14,15,16,13,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4671 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4671_checked : acceptsGraphIso
    (source (graph core4671) (root 10) 2 2) DegreeTwoThreeSpectrum7470.graph sourceMap4671=true := by decide +kernel
theorem fusedMap4671_checked : acceptsGraphIso
    (fused (graph core4671) (root 10) 2 2) DegreeTwoThreeSpectrum5600.graph fusedMap4671=true := by decide +kernel
theorem certified4671 : Certified (graph core4671) (root 10) 2 2 :=
  of_native_maps core4671 DegreeTwoThreeSpectrum7470.graph DegreeTwoThreeSpectrum5600.graph
    sourceMap4671 fusedMap4671 sourceMap4671_checked fusedMap4671_checked
    DegreeTwoThreeFiniteComparisons.comparison4671
#print axioms sourceMap4671_checked
#print axioms fusedMap4671_checked
#print axioms certified4671
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
