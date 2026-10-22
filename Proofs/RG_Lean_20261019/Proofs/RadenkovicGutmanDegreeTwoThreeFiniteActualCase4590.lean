/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4590 : Family 10 := level10.get ⟨571,by decide⟩
def sourceMap4590 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4590 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4590_checked : acceptsGraphIso
    (source (graph core4590) (root 10) 2 2) DegreeTwoThreeSpectrum7202.graph sourceMap4590=true := by decide +kernel
theorem fusedMap4590_checked : acceptsGraphIso
    (fused (graph core4590) (root 10) 2 2) DegreeTwoThreeSpectrum5236.graph fusedMap4590=true := by decide +kernel
theorem certified4590 : Certified (graph core4590) (root 10) 2 2 :=
  of_native_maps core4590 DegreeTwoThreeSpectrum7202.graph DegreeTwoThreeSpectrum5236.graph
    sourceMap4590 fusedMap4590 sourceMap4590_checked fusedMap4590_checked
    DegreeTwoThreeFiniteComparisons.comparison4590
#print axioms sourceMap4590_checked
#print axioms fusedMap4590_checked
#print axioms certified4590
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
