/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4515 : Family 10 := level10.get ⟨340,by decide⟩
def sourceMap4515 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4515 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4515_checked : acceptsGraphIso
    (source (graph core4515) (root 10) 2 2) DegreeTwoThreeSpectrum6742.graph sourceMap4515=true := by decide +kernel
theorem fusedMap4515_checked : acceptsGraphIso
    (fused (graph core4515) (root 10) 2 2) DegreeTwoThreeSpectrum5594.graph fusedMap4515=true := by decide +kernel
theorem certified4515 : Certified (graph core4515) (root 10) 2 2 :=
  of_native_maps core4515 DegreeTwoThreeSpectrum6742.graph DegreeTwoThreeSpectrum5594.graph
    sourceMap4515 fusedMap4515 sourceMap4515_checked fusedMap4515_checked
    DegreeTwoThreeFiniteComparisons.comparison4515
#print axioms sourceMap4515_checked
#print axioms fusedMap4515_checked
#print axioms certified4515
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
