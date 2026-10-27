/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4246 : Family 9 := level9.get ⟨203,by decide⟩
def sourceMap4246 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4246 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4246_checked : acceptsGraphIso
    (source (graph core4246) (root 9) 2 2) DegreeTwoThreeSpectrum4800.graph sourceMap4246=true := by decide +kernel
theorem fusedMap4246_checked : acceptsGraphIso
    (fused (graph core4246) (root 9) 2 2) DegreeTwoThreeSpectrum3985.graph fusedMap4246=true := by decide +kernel
theorem certified4246 : Certified (graph core4246) (root 9) 2 2 :=
  of_native_maps core4246 DegreeTwoThreeSpectrum4800.graph DegreeTwoThreeSpectrum3985.graph
    sourceMap4246 fusedMap4246 sourceMap4246_checked fusedMap4246_checked
    DegreeTwoThreeFiniteComparisons.comparison4246
#print axioms sourceMap4246_checked
#print axioms fusedMap4246_checked
#print axioms certified4246
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
