/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4982 : Family 10 := level10.get ⟨1577,by decide⟩
def sourceMap4982 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4982 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4982_checked : acceptsGraphIso
    (source (graph core4982) (root 10) 2 2) DegreeTwoThreeSpectrum7583.graph sourceMap4982=true := by decide +kernel
theorem fusedMap4982_checked : acceptsGraphIso
    (fused (graph core4982) (root 10) 2 2) DegreeTwoThreeSpectrum6057.graph fusedMap4982=true := by decide +kernel
theorem certified4982 : Certified (graph core4982) (root 10) 2 2 :=
  of_native_maps core4982 DegreeTwoThreeSpectrum7583.graph DegreeTwoThreeSpectrum6057.graph
    sourceMap4982 fusedMap4982 sourceMap4982_checked fusedMap4982_checked
    DegreeTwoThreeFiniteComparisons.comparison4982
#print axioms sourceMap4982_checked
#print axioms fusedMap4982_checked
#print axioms certified4982
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
