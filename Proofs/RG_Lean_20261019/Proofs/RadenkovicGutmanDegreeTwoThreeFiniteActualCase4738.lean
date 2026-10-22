/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4738 : Family 10 := level10.get ⟨968,by decide⟩
def sourceMap4738 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4738 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4738_checked : acceptsGraphIso
    (source (graph core4738) (root 10) 2 2) DegreeTwoThreeSpectrum7431.graph sourceMap4738=true := by decide +kernel
theorem fusedMap4738_checked : acceptsGraphIso
    (fused (graph core4738) (root 10) 2 2) DegreeTwoThreeSpectrum5887.graph fusedMap4738=true := by decide +kernel
theorem certified4738 : Certified (graph core4738) (root 10) 2 2 :=
  of_native_maps core4738 DegreeTwoThreeSpectrum7431.graph DegreeTwoThreeSpectrum5887.graph
    sourceMap4738 fusedMap4738 sourceMap4738_checked fusedMap4738_checked
    DegreeTwoThreeFiniteComparisons.comparison4738
#print axioms sourceMap4738_checked
#print axioms fusedMap4738_checked
#print axioms certified4738
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
