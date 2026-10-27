/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4234 : Family 9 := level9.get ⟨168,by decide⟩
def sourceMap4234 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4234 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4234_checked : acceptsGraphIso
    (source (graph core4234) (root 9) 2 2) DegreeTwoThreeSpectrum4753.graph sourceMap4234=true := by decide +kernel
theorem fusedMap4234_checked : acceptsGraphIso
    (fused (graph core4234) (root 9) 2 2) DegreeTwoThreeSpectrum3930.graph fusedMap4234=true := by decide +kernel
theorem certified4234 : Certified (graph core4234) (root 9) 2 2 :=
  of_native_maps core4234 DegreeTwoThreeSpectrum4753.graph DegreeTwoThreeSpectrum3930.graph
    sourceMap4234 fusedMap4234 sourceMap4234_checked fusedMap4234_checked
    DegreeTwoThreeFiniteComparisons.comparison4234
#print axioms sourceMap4234_checked
#print axioms fusedMap4234_checked
#print axioms certified4234
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
